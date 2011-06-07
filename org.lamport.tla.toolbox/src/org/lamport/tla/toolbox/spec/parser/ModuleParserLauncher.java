package org.lamport.tla.toolbox.spec.parser;

import java.io.PrintStream;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.nature.TLAParsingBuilderConstants;
import org.lamport.tla.toolbox.ui.handler.ParseSpecHandler;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.RCPNameToFileIStream;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.TLAMarkerInformationHolder;

import tla2sany.drivers.InitException;
import tla2sany.drivers.SANY;
import tla2sany.drivers.SemanticException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import util.FilenameToStream;
import util.ToolIO;
import util.UniqueString;

/**
 * This parser launcher starts SANY and uses SANY's console output to find errors
 * 
 * 
 * @author Leslie Lamport, Simon Zambrovski
 * @version $Id$
 */
public class ModuleParserLauncher
{
    /**
     * A shortcut for parseModule(parseResource, monitor, true, true)
     * This parses the module, update the dependencies and handles markers  
     */
    public ParseResult parseModule(IResource parseResource, IProgressMonitor monitor)
    {
        return parseModule(parseResource, monitor, true, true);
    }

    /**
     * Parses the given module and installs error markers on it (or project)
     * @param parseResource
     * @param monitor
     * @param installMarker a boolean flag indicating if the markers on the resource should be handled
     * @return
     */
    public ParseResult parseModule(IResource parseResource, IProgressMonitor monitor, boolean installMarkers,
            boolean updateStorage)
    {
        // get the project
        IProject project = parseResource.getProject();

        // setup the directory of the file
        ToolIO.setUserDir(ResourceHelper.getParentDirName(parseResource.getLocation().toOSString()));

        // reset problems from previous run
        if (installMarkers)
        {
            TLAMarkerHelper.removeProblemMarkers(parseResource, monitor,
                    TLAMarkerHelper.TOOLBOX_MARKERS_TLAPARSER_MARKER_ID);
        }

        // call the parsing
        ParseResult result = parseModule(parseResource, monitor, updateStorage);
        
        // should cancel?
        checkCancel(monitor);

        if (updateStorage)
        {
            // reset the module dependency storage
            if (AdapterFactory.isProblemStatus(result.getStatus()))
            {
                Activator.getModuleDependencyStorage().parseFailed(parseResource.getProjectRelativePath().toString());
            }
        }

        // process the errors, the method perform changes on the parseResult
        processParsingErrors(project, result);

        // store errors inside the specification project
        if (installMarkers)
        {
            TLAMarkerHelper.installProblemMarkers(result.getDetectedErrors(), monitor);
        }

        return result;
    }

    /**
     * Calls SANY, that parses the root module. <br>
     * <b>Note:</b> This method fills the error objects {@link ParseSpecHandler#parseErrors} and
     * {@link ParseSpecHandler#semanticErrors}. Call {@link ParseSpecHandler#processParsingErrors(Spec)} to store this
     * information in the specification handle
     * 
     * @param doSemanticAnalysis
     *            if true, the semantical phase will be started
     * @param parseResource
     *            filename of the module to parse
     * @param monitor 
     * @return status of parsing, one of the {@link IParseConstants} constants
     */
    private ParseResult parseModule(IResource parseResource, IProgressMonitor monitor, boolean updateStorage)
    {
        String moduleFilename = parseResource.getLocation().toOSString();

        // one of the Spec constants
        int specStatus = 0;

        Errors parseErrors = null;
        Errors semanticErrors = null;

        FilenameToStream resolver = new RCPNameToFileIStream(null);

        // Reset the tool output messages.
        ToolIO.reset();
        ToolIO.setDefaultResolver(resolver);
        ToolIO.setMode(ToolIO.TOOL);

        // Initialize the module variables
        SpecObj moduleSpec = new SpecObj(ResourceHelper.getModuleName(moduleFilename), resolver);

        // The parsing methods take a PrintStream on which they print out some
        // (but hardly all) error messages.
        // They're called with this one.
        PrintStream outputStr = ToolIO.out;

        // get the time stamp for the call of the parser
        long parserCallTime = System.currentTimeMillis();

        try
        {
            // should cancel?
            checkCancel(monitor);
            SANY.frontEndInitialize(moduleSpec, outputStr);
            // should cancel?
            checkCancel(monitor);
            SANY.frontEndParse(moduleSpec, outputStr);
            // should cancel?
            checkCancel(monitor);
            SANY.frontEndSemanticAnalysis(moduleSpec, outputStr, true);
            // should cancel?
            checkCancel(monitor);
        } catch (InitException e)
        {
            // set spec status
            specStatus = IParseConstants.UNKNOWN_ERROR;
            return new ParseResult(specStatus, null, parseResource, parseErrors, semanticErrors, parserCallTime);

        } catch (ParseException e)
        {
            // I believe that this exception is thrown iff there is a parsing
            // error.
            specStatus = IParseConstants.SYNTAX_ERROR;
            parseErrors = moduleSpec.getParseErrors();
        } catch (SemanticException e)
        {

            // This exception is apparently thrown only by
            // frontEndSemanticAnalysis if the semantic analysis throws an
            // AbortException.
            specStatus = IParseConstants.SEMANTIC_ERROR;
        }

        // Compute the return value and set semanticErrors.
        if (specStatus > IParseConstants.SYNTAX_ERROR)
        {
            semanticErrors = moduleSpec.semanticErrors;
            if (semanticErrors != null)
            {
                // add global context errors to semantic errors because they should
                // be treated the same way by the toolbox
                // these errors include defining the same operator
                // in two different modules that are extended
                Errors globalContextErrors = moduleSpec.getGlobalContextErrors();

                // globalContextErrors contains errors, aborts, and warnings
                // each should be added to semanticErrors
                String[] errors = globalContextErrors.getErrors();
                for (int i = 0; i < errors.length; i++)
                {
                    semanticErrors.addError(null, errors[i]);
                }

                String[] aborts = globalContextErrors.getAborts();
                for (int i = 0; i < aborts.length; i++)
                {
                    try
                    {
                        semanticErrors.addAbort(aborts[i], false);
                    } catch (AbortException e)
                    {
                        Activator.logDebug("Abort exception thrown in ModuleParserLauncher."
                                + "This is a bug. There should not be an AbortException thrown here.");
                    }
                }

                String[] warnings = globalContextErrors.getWarnings();
                for (int i = 0; i < warnings.length; i++)
                {
                    semanticErrors.addWarning(null, warnings[i]);
                }

                if (semanticErrors.getNumMessages() > 0)
                {
                    if (semanticErrors.isSuccess())
                    {
                        specStatus = IParseConstants.SEMANTIC_WARNING;
                    } else
                    {
                        specStatus = IParseConstants.SEMANTIC_ERROR;
                    }
                } // if (semanticErrors.getNumMessages() > 0)
            } // if (semanticErrors != null)
        } // if (returnVal > SYNTAX_ERROR)

        // Compute userModules and standardModules.
        // Set the moduleNode components only if there were no parsing or
        // semantic errors.

        Vector userModules = new Vector();
        // Vector standardModules = new Vector();
        boolean rootModuleFound = false;

        final Vector resourcesToTimeStamp = new Vector();

        // iterate over parse units
        Enumeration enumerate = moduleSpec.parseUnitContext.keys();
        while (enumerate.hasMoreElements())
        {
            // should cancel?
            checkCancel(monitor);
        	
            // This enumeration finds all non-inner modules in the spec.
            String moduleName = (String) enumerate.nextElement();
            ParseUnit parseUnit = (ParseUnit) moduleSpec.parseUnitContext.get(moduleName);

            String absoluteFileName = null;
            if (parseUnit.getNis() != null && parseUnit.getNis().sourceFile() != null)
            {
                absoluteFileName = parseUnit.getNis().sourceFile().getAbsolutePath();
            }
            if (absoluteFileName == null)
            {
                throw new RuntimeException("Bug: Spec.ParseMainModule:1730");
            }

            // create module holder
            Module module = new Module(absoluteFileName);

            if (!module.isStandardModule() && updateStorage)
            {

                IResource moduleResource = ResourceHelper.getResourceByModuleName(moduleName);
                if (moduleResource != null && moduleResource.exists())
                {
                    resourcesToTimeStamp.add(moduleResource);
                }
            }

            // semantic module only available if no semantic errors found
            if (specStatus > IParseConstants.SEMANTIC_ERROR)
            {
                ExternalModuleTable.ExternalModuleTableEntry emt = (ExternalModuleTable.ExternalModuleTableEntry) moduleSpec
                        .getExternalModuleTable().moduleHashTable.get(UniqueString.uniqueStringOf(module
                        .getModuleName()));
                if (emt != null)
                {
                    module.setNode(emt.getModuleNode());
                }
            }

            if (module.getModuleName().equals(ResourceHelper.getModuleName(moduleFilename)))
            {
                rootModuleFound = true;
                module.setRoot(true);
            }

            if (module.isStandardModule())
            {
                // standardModules.addElement(module);
            } else
            {
                // if the module is not a standard module
                userModules.addElement(module);

                // check whether the absolute filename of the module contains an
                // absolute filename of the project
                // if yes, that means that the module is resides (in the FS)
                // inside of the project directory
                // and no linking is required
                if (module.getAbsolutePath().indexOf(parseResource.getProject().getLocation().toOSString()) != 0)
                {
                    // create a link to the module, so we could open it
                    ResourceHelper.getLinkedFile(parseResource.getProject(), module.getAbsolutePath(), true);
                }
            }

        } // while

        // This is used to properly update the spec parse status on resource modifications
        // by setting the last build time stamp
        try
        {
            ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {

                public void run(IProgressMonitor monitor) throws CoreException
                {
                    Iterator iterator = resourcesToTimeStamp.iterator();
                    while (iterator.hasNext())
                    {
                        IResource resource = (IResource) iterator.next();
                        resource.setPersistentProperty(TLAParsingBuilderConstants.LAST_BUILT, String.valueOf(System
                                .currentTimeMillis()));
                    }
                }
            }, new NullProgressMonitor());
        } catch (CoreException e)
        {
            Activator.logError("Error while setting build timestamp on resource.", e);
        }

        if (!rootModuleFound)
        {
            specStatus = IParseConstants.COULD_NOT_FIND_MODULE;
        }

        if (updateStorage)
        {
            // at this point the user modules are known
            // store the dependencies
            Activator.getModuleDependencyStorage().put(parseResource.getName(),
                    AdapterFactory.adaptModules(parseResource.getName(), userModules));
        }

        // remove the modules
        // for (int i = userModules.size(); i > 0; i--)
        // {
        // ((Module)userModules.remove(i-1)).destroy();
        // }
        // userModules = null;

        // broadcast new parse result
        ParseResult parseResult = new ParseResult(specStatus, moduleSpec, parseResource, parseErrors, semanticErrors,
                parserCallTime);
        ParseResultBroadcaster.getParseResultBroadcaster().broadcastParseResult(parseResult);

        return parseResult;/*new ParseResult(specStatus, moduleSpec, parseResource, parseErrors, semanticErrors);*/
    }

    /**
     * Parses console outputs produced during the run of SANY and transform them into error object, which are stored
     * inside the specification object <br>
     * <b>Note:</b> this method is based on the status of the spec ({@link Spec#getStatus()}) and cleans up the error
     * objects {@link ParseHandler#parseErrors} and {@link ParseHandler#semanticErrors}
     * 
     * @param spec
     *            specification handle
     */
    /**
     * First try to get the information from parser's printed output.<br>
     * Here's what I've found out about messages when there's a parsing error. The message with the error
     * looks like one of the following: <br>
     * - "Lexical error at line n, column n." + message<br>
     * <br>
     * - "***Parse Error***"\n + Message + "at line n, column n" <br>
     * + Message<br>
     * <br>
     * - "Parse Error\n\n Precedence conflict between<br>
     * ops /\ in block line n, col m to line m, col<br>
     * of module Foo and \/ " + message<br>
     * <br>
     * The preceding message is<br>
     * <br>
     * "Parsing module Naturals in file<br>
     * C:\\users\lamport ...\Naturals.tla"<br>
     * <br>
     * which is produced by a call to ToolIO.out.println in<br>
     * ParseUnit.parseFile<br>
     * <br>
     * When such a message is produced, the parseErrors just contains<br>
     * a single abort that is useless. However, the preceding kind of<br>
     * error message isn't produced for the following kinds of errors:<br>
     * <br>
     * 1. A module's file can't be read.<br>
     * 2. There's a circular EXTENDS/INSTANCES dependency.<br>
     * 3. The module name is different from the file name.<br>
     * <br>
     * The abort is "Unknown location\n\n" + message, where message<br>
     * is:<br>
     * <br>
     * 1. "Cannot find source file for module Foo"<br>
     * 2. "Circular dependency among .tla files; dependency cycle..."<br>
     * 3. "File name 'Foo' does not match the name 'Foobar"" of the<br>
     * top level module it contains."<br>
     * In the first two errors, the last "Parsing module" message does not contain the name of the module
     * with the error, and there seems to be no way to figure out in what module the error is.<br>
     * The first type of message also includes the following rare variants.<br>
     * <br>
     * - "Error: Failed to open output file Foo\n ..." which occurs if there's an IOException.<br>
     * - "Error: source file 'Foo' has apparently been deleted." which occurs I have no idea when<br>
     * There's also<br>
     * - "Could not parse module Foo from file FooBar"<br>
     * I have no idea when that is produced.
     */
    private void processParsingErrors(IProject project, ParseResult result)
    {

        switch (result.getStatus()) {
        /* ------------------ SYNTAX ERRORS --------------------- */

        case IParseConstants.SYNTAX_ERROR:

            String[] output = ToolIO.getAllMessages();
            int nextMsg = 0;

            // The following was modified by lamport on 5 Sep 2009 to add the
            // special case
            // handling of an error caused by importing a non-existent module.
            //
            // This code depends on the exact syntax of error messages produced
            // by SANY.
            // If those messages change in any way, the code will break.
            //
            // Set module name and leave nextMsg the index of the error message.
            // We do this by first finding the last module name Foo for which
            // SANY output
            // "Parsing module foo".
            while ((nextMsg < output.length) && (output[nextMsg].indexOf("Parsing module") != -1))
            {
                nextMsg++;
            }

            if ((nextMsg != 0) && (nextMsg != output.length))
            {
                // find out the module name
                int parsingModuleIndex = output[nextMsg - 1].indexOf("Parsing module") + 15;
                String nameToFind = output[nextMsg - 1].substring(parsingModuleIndex, output[nextMsg - 1].indexOf(" ",
                        parsingModuleIndex + 1));

                // Test for special case of importing unknown module. (added 5
                // Sep 2009 by lamport)
                String[] abortMsgs = result.getParseErrors().getAborts();
                if ((abortMsgs.length > 0) && (abortMsgs[0].indexOf("Cannot find source file for module") != -1))
                {
                    parsingModuleIndex = abortMsgs[0].indexOf("imported in module ") + 19;
                    nameToFind = abortMsgs[0].substring(parsingModuleIndex, abortMsgs[0].indexOf(".",
                            parsingModuleIndex + 1));
                }

                // Correct the capitalization of nameToFind, if necessary.
                // See description of the correctModuleNameCapitalization method.
                nameToFind = correctModuleNameCapitalization(nameToFind, result);
                IFile module = ResourceHelper.getLinkedFile(result.getParsedResource().getParent(), ResourceHelper
                        .getModuleFileName(nameToFind), false);

                // coordinates of the error
                int[] coordinates = new int[] { -1, -1, -1, -1 };
                // The error message
                String message = output[nextMsg];

                if ((message.indexOf("Lexical error") != -1) || (message.indexOf("***Parse Error***") != -1))
                {
                    // This is a meaningful error message and should have at
                    // least
                    // one line, column number.
                    int[] val = findLineAndColumn(0, message);
                    int beginLine = val[0];
                    int beginColumn = val[1];
                    int endLine = 0;
                    int endColumn = 0;

                    val = findLineAndColumn(val[2], message);

                    // Set endLine, endColumn if position val[0], val[1] is
                    // after beginLine, beginColumn.
                    if ((val[0] > beginLine) || ((val[0] == beginLine) && (val[1] >= beginColumn)))
                    {
                        endLine = val[0];
                        endColumn = val[1];
                    }

                    // coordinates of the error
                    coordinates = new int[] { beginLine, beginColumn, endLine, endColumn };

                    // If the message doesn't contain the module name, we
                    // should add it.

                    // Added by Ricketts on Sept 7 2009
                    // This adds the module name which is not in the error message returned by sany in syntactic errors.
                    String beforeModuleName = message.substring(0, findLineAndColumn(0, message)[2]);
                    String afterModuleName = message.substring(findLineAndColumn(0, message)[2]);
                    message = beforeModuleName + " in module "
                            + module.getName().substring(0, module.getName().length() - 4) + afterModuleName;

                    result.addMarker(new TLAMarkerInformationHolder(module, module.getName(), IMarker.SEVERITY_ERROR,
                            coordinates, message));
                } // if
                else
                {

                    // This is not a meaningful error message; get the message
                    // from
                    // the abort in parseErrors
                    if (result.getParseErrors() != null)
                    {
                        String[] aborts = result.getParseErrors().getAborts();
                        if (aborts.length > 0)
                        {
                            // error message
                            message = aborts[0];
                        }
                    }
                    // Unless this is the one abort in which err.moduleName can
                    // be
                    // computed from the error messages, reset it to "".
                    if (message != null && message.indexOf("does not match the name") == -1)
                    {
                        coordinates = new int[] { -1, -1, -1, -1 };
                        // coordinates[0] = 1 ; coordinates[1] = 1 ;
                        // coordinates[2] = 1 ; coordinates[3] = 1;

                    }
                    if (module == null)
                    {
                        result.addMarker(new TLAMarkerInformationHolder(project, project.getName(),
                                IMarker.SEVERITY_ERROR, coordinates, message));
                    } else
                    {
                        result.addMarker(new TLAMarkerInformationHolder(module, module.getName(),
                                IMarker.SEVERITY_ERROR, coordinates, message));
                    }

                } // else

            } // if
            else
            {
                throw new RuntimeException("Bug Spec.ProcessParsingErrorMessages:1869.\n" + "Can't find module name");
            } // else
            break;

        /* ------------------ SEMANTIC ERRORS AND WARNINGS --------------------- */
        case IParseConstants.SEMANTIC_ERROR:
        case IParseConstants.SEMANTIC_WARNING:
            // There were semantic errors or warnings
            if (result.getSemanticErrors() != null)
            {

                String[][] errors = { result.getSemanticErrors().getAborts(), result.getSemanticErrors().getErrors(),
                        result.getSemanticErrors().getWarnings() };
                int[] holderType = { IMarker.SEVERITY_ERROR, IMarker.SEVERITY_ERROR, IMarker.SEVERITY_WARNING };

                for (int j = 0; j < 3; j++)
                {
                    for (int i = 0; i < errors[j].length; i++)
                    {
                        // encodeSematicErrorFromString(project,
                        // result.getParsedResource(), errors[j][i],
                        // holderType[j], monitor);
                        IFile module = null;

                        // Get pair of line, column numbers
                        int[] val = findLineAndColumn(0, errors[j][i]);
                        int beginLine = val[0];
                        int beginColumn = val[1];
                        int endLine = 0;
                        int endColumn = 0;

                        val = findLineAndColumn(val[2], errors[j][i]);
                        if ((val[0] > beginLine) || ((val[0] == beginLine) && (val[1] >= beginColumn)))
                        {
                            endLine = val[0];
                            endColumn = val[1];
                        }

                        // Get module name. We use the fact that errors and
                        // warnings are always generated with the
                        // module, indicated by " module Name\n". *
                        int beginModuleIdx = errors[j][i].indexOf(" module ");
                        if (beginModuleIdx != -1)
                        {
                            beginModuleIdx = beginModuleIdx + " module ".length();
                            int endModuleIdx = errors[j][i].indexOf("\n", beginModuleIdx);
                            if (endModuleIdx != -1)
                            {
                                // Correct the capitalization of the name in the error message.
                                // See description of the correctModuleNameCapitalization method.
                                String nameToFind = correctModuleNameCapitalization(errors[j][i].substring(
                                        beginModuleIdx, endModuleIdx), result);

                                module = ResourceHelper.getLinkedFile(result.getParsedResource().getParent(),

                                ResourceHelper.getModuleFileName(nameToFind), false);
                            }
                        }

                        int[] coordinates = new int[] { beginLine, beginColumn, endLine, endColumn };

                        if (module == null)
                        {
                            result.addMarker(new TLAMarkerInformationHolder(project, project.getName(), holderType[j],
                                    coordinates, errors[j][i]));

                        } else
                        {
                            result.addMarker(new TLAMarkerInformationHolder(module, module.getName(), holderType[j],
                                    coordinates, errors[j][i]));
                        }

                    }
                }// for i, for j

            } else
            {
                throw new RuntimeException("Bug Spec.ProcessParsingErrorMsgs.1418:\n"
                        + "Semantic error detected but no error message found.");
            }
            break;
        case IParseConstants.COULD_NOT_FIND_MODULE:

            result.addMarker(new TLAMarkerInformationHolder(project, project.getName(), IMarker.SEVERITY_ERROR,
                    new int[] { -1, -1, -1, -1 }, "Could not find module"));
            break;
        case IParseConstants.PARSED:
            break;
        default:
            throw new RuntimeException("No default expected. Still spec.getStatus() returned a value of "
                    + result.getStatus());
        }
    } // ProcessParsingErrorMsgs

    /**
     * Hack added by lamport on 5 & 7 Sep 2009
     This method is called in two places above to provide a file
     name argument to ResourceHelper.getLinkedFile.
     
     If a module name differs in case from the file name--for example,
     if module Foo is in file foo.tla--the code that finds the module 
     name from Sany's error messages sometimes finds the module name
     rater than the file name.  Because
     the Eclipse resource lookup methods seem to be case sensitive, this
     causes the calls to ResourceHelper.getLinkedFile  not to find
     the file, causing an exception somewhere down the line that
     prevents the Parsing Error view from being raised.  The following
     method sees if there is a resource file having the same name as nameToFind
     if case is ignored and, if there is, it returns that resource
     name.  (I have no idea exactly when the files being parsed get added
     to the resources, but it seems to happen early enough in the game
     for this to work.)
     */
    private static final String correctModuleNameCapitalization(String nameToFind, ParseResult result)
    {
        try
        {
            IResource[] resources = result.getParsedResource().getParent().members();
            for (int i = 0; i < resources.length; i++)
            {
                if (resources[i].getType() == IResource.FILE)
                {
                    String resourceName = resources[i].getName().substring(0, resources[i].getName().length() - 4);
                    if ((nameToFind.toLowerCase()).equals(resourceName.toLowerCase()))
                    {
                        nameToFind = resourceName;
                        break;
                    }
                }
            }
        } catch (CoreException e)
        {
            Activator.logError("Error finding modules", e);
        }
        return nameToFind;
    }

    /**
     * Looks for line and column number in str starting at idx, and returns a 3-element array val with val[0] = the line
     * number and val[1] = the column number, and val[2] the index at the end of the column number. It returns -1 for a
     * number it doesn't find, and may leave val[3] off the end of the array. It works (but of course finds nothing if
     * idx >= str.length(). This is a kludge that assumes that the line number is preceded either by " line " or by
     * "line " that begins the error message, and that the column number is preceded by either " column " or " col ".
     * 
     * Bug found on 17 Oct 2010:  On some errors, SANY returns an error message with location
     * 
     *    line 2147483647, col 2147483647 to line -2147483648, col -2147483648
     *    
     * One such error is caused by
     * 
     *    BY DEF Foo.x'
     *    
     * in a proof.  Such a line or column number produces a java.lang.NumberFormatException
     * when Integer.parseInt is called to parse it.  Perhaps this should be fixed in SANY.  
     * However, even if that were to be fixed, it seems like a good idea to catch the 
     * exception here in case there are other cases in which SANY produces a malformed
     * location.  So this was done by LL on 17 Oct 2010.  The fix is to return values
     * of -1 when an exception is thrown, hoping that the comment is accurate and the
     * return value of -1 is expected by the caller.
     */
    private static final int[] findLineAndColumn(final int idx, final String message)
    {
        int[] val = /* new int[3] */{ -1, -1, message.length() };

        /***********************************************************************
         * Search for either " line " or "line " starting at idx. 
         *
         ***********************************************************************/
        int beginIndex = message.indexOf("line ", idx);
        int offset = 5;
        if (beginIndex != idx)
        {
            beginIndex = -1;
        }
        if (beginIndex == -1)
        {
            beginIndex = message.indexOf(" line ", idx);
            offset = 6;
        }
        if (beginIndex != -1)
        {
            /***************************************************************
             * Found " line ". Set beginIndex, endLineIndex to the 
             * beginning and past the end of the line number. 
             *
             ***************************************************************/
            beginIndex = beginIndex + offset;
            while ((beginIndex < message.length()) && !Character.isDigit(message.charAt(beginIndex)))
            {
                beginIndex++;
            }
            int endIndex = beginIndex + 1;
            while ((endIndex < message.length()) && Character.isDigit(message.charAt(endIndex)))
            {
                endIndex++;
            }
            if (beginIndex < message.length())
            {
                /*******************************************************************
                 * Valid values of beginIndex and endIndex, so set val[0] and look 
                 * for the column number. 
                 *
                 *******************************************************************/
                try
                {
                    val[0] = Integer.parseInt(message.substring(beginIndex, endIndex));
                } catch (Exception e)
                {
                    val[0] = -1;
                }
                beginIndex = message.indexOf(" column ", endIndex);
                int colOffset = 0; // to keep compiler happy.
                if (beginIndex != -1)
                {
                    colOffset = 8;
                }
                int otherIndex = message.indexOf(" col ", endIndex);
                if ((otherIndex != -1) && ((beginIndex == -1) || (otherIndex < beginIndex)))
                {
                    beginIndex = otherIndex;
                    colOffset = 5;
                } // else
                if (beginIndex != -1)
                {
                    /*****************************************************************
                     * Found either " column " or " col ". Set beginIndex, endIndex 
                     * to the beginning and past the end
                     * of the line number. 
                     *
                     *****************************************************************/
                    beginIndex = beginIndex + colOffset;
                    while ((beginIndex < message.length()) && !Character.isDigit(message.charAt(beginIndex)))
                    {
                        beginIndex++;
                    } // while
                    endIndex = beginIndex + 1;
                    while ((endIndex < message.length()) && Character.isDigit(message.charAt(endIndex)))
                    {
                        endIndex++;
                    }
                    if (beginIndex < message.length())
                    {
                        /***************************************************************
                         * Valid values of beginIndex and endIndex, so set val[1] and val[2].
                         ***************************************************************/
                        try
                        {
                            val[1] = Integer.parseInt(message.substring(beginIndex, endIndex));
                        } catch (Exception e)
                        {
                            val[1] = -1;
                        }
                        val[2] = endIndex;
                    } // if (beginIndex < str.length())
                } // if (beginIndex != -1)
            } // if (beginIndex < str.length())
        } // if (beginIndex != -1)
        return val;
    } // findLineAndColumn

    /**
     * This is how the workbench signals a click on the cancel button or if
     * the workbench has been shut down in the meantime.
     * 
     * @see http://www.eclipse.org/articles/Article-Builders/builders.html
     */
    protected void checkCancel(IProgressMonitor monitor) {
        if (monitor.isCanceled()) {
           throw new OperationCanceledException();
        }
     }
}
