package org.lamport.tla.toolbox.spec.parser;

import java.io.PrintStream;
import java.util.Enumeration;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.handler.ParseSpecHandler;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.TLAMarkerInformationHolder;
import org.lamport.tla.toolbox.util.RCPNameToFileIStream;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;

import tla2sany.drivers.InitException;
import tla2sany.drivers.SANY;
import tla2sany.drivers.SemanticException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
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
        ParseResult result = parseModule(parseResource, true);

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
     * @return status of parsing, one of the {@link IParseConstants} constants
     */
    private ParseResult parseModule(IResource parseResource, boolean doSemanticAnalysis)
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

        // The parsing methods take a PrintStream on which they print out some (but hardly all) error messages.
        // They're called with this one.
        PrintStream outputStr = ToolIO.err;

        try
        {
            SANY.frontEndInitialize(moduleSpec, outputStr);
            SANY.frontEndParse(moduleSpec, outputStr);
            if (doSemanticAnalysis)
            {
                SANY.frontEndSemanticAnalysis(moduleSpec, outputStr, true);
            }
        } catch (InitException e)
        {
            // set spec status
            specStatus = IParseConstants.UNKNOWN_ERROR;
            return new ParseResult(specStatus, null, parseResource, parseErrors, semanticErrors);

        } catch (ParseException e)
        {
            // I believe that this exception is thrown iff there is a parsing error.
            specStatus = IParseConstants.SYNTAX_ERROR;
            parseErrors = moduleSpec.getParseErrors();
        } catch (SemanticException e)
        {

            // This exception is apparently thrown only by frontEndSemanticAnalysis if the semantic analysis throws an
            // AbortException.
            specStatus = IParseConstants.SEMANTIC_ERROR;
        }

        // Compute the return value and set semanticErrors.
        if (specStatus > IParseConstants.SYNTAX_ERROR)
        {
            semanticErrors = moduleSpec.semanticErrors;
            if (semanticErrors != null)
            {
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
        // Set the moduleNode components only if there were no parsing or semantic errors.

        Vector userModules = new Vector();
        Vector standardModules = new Vector();
        boolean rootModuleFound = false;

        // iterate over parse units
        Enumeration enumerate = moduleSpec.parseUnitContext.keys();
        while (enumerate.hasMoreElements())
        {
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

            if (!module.isStandardModule())
            {
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
                standardModules.addElement(module);
            } else
            {
                // if the module is not a standard module
                userModules.addElement(module);

                // check whether the absolute filename of the module contains an absolute filename of the project
                // if yes, that means that the module is resides (in the FS) inside of the project directory
                // and no linking is required
                if (module.getAbsolutePath().indexOf(parseResource.getProject().getLocation().toOSString()) != 0)
                {
                    // create a link to the module, so we could open it
                    ResourceHelper.getLinkedFile(parseResource.getProject(), module.getAbsolutePath(), true);
                }
            }

        } // while

        if (!rootModuleFound)
        {
            specStatus = IParseConstants.COULD_NOT_FIND_MODULE;
        }

        // at this point the user modules are known
        // store the dependencies
        Activator.getModuleDependencyStorage().put(parseResource.getName(),
                AdapterFactory.adaptModules(parseResource.getName(), userModules));

        return new ParseResult(specStatus, moduleSpec, parseResource, parseErrors, semanticErrors);
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

            // Set module name and leave nextMsg the index of the error message.
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

                IFile module = ResourceHelper.getLinkedFile(result.getParsedResource().getParent(), ResourceHelper
                        .getModuleFileName(nameToFind), false);

                // coordinates of the error
                int[] coordinates = new int[] { -1, -1, -1, -1 };

                // The error message
                String message = output[nextMsg];

                if ((message.indexOf("Lexical error") != -1) || (message.indexOf("***Parse Error***") != -1))
                {
                    // This is a meaningful error message and should have at least
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

                    result.addMarker(new TLAMarkerInformationHolder(module, module.getName(), IMarker.SEVERITY_ERROR,
                            coordinates, message));
                } // if
                else
                {

                    // This is not a meaningful error message; get the message from
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
                    // Unless this is the one abort in which err.moduleName can be
                    // computed from the error messages, reset it to "".
                    if (message != null && message.indexOf("does not match the name") == -1)
                    {
                        coordinates = new int[] { -1, -1, -1, -1 };
                    }
                    if (module == null)
                    {
                        result.addMarker(new TLAMarkerInformationHolder(project, project.getName(),
                                IMarker.SEVERITY_ERROR, coordinates, message));
                    } else
                    {
                        result.addMarker(new TLAMarkerInformationHolder(module, module.getName(), IMarker.SEVERITY_ERROR,
                                coordinates, message));
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
            if (result.getParseErrors() != null)
            {

                String[][] errors = { result.getParseErrors().getAborts(), result.getParseErrors().getErrors(),
                        result.getParseErrors().getWarnings() };
                int[] holderType = { IMarker.SEVERITY_ERROR, IMarker.SEVERITY_ERROR, IMarker.SEVERITY_WARNING };

                for (int j = 0; j < 3; j++)
                {
                    for (int i = 0; i < errors[j].length; i++)
                    {
                        // encodeSematicErrorFromString(project, result.getParsedResource(), errors[j][i],
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

                        // Get module name. We use the fact that errors and warnings are always generated with the
                        // module, indicated by " module Name\n". *
                        int beginModuleIdx = errors[j][i].indexOf(" module ");
                        if (beginModuleIdx != -1)
                        {
                            beginModuleIdx = beginModuleIdx + " module ".length();
                            int endModuleIdx = errors[j][i].indexOf("\n", beginModuleIdx);
                            if (endModuleIdx != -1)
                            {
                                module = ResourceHelper.getLinkedFile(result.getParsedResource().getParent(),
                                        ResourceHelper.getModuleFileName(errors[j][i].substring(beginModuleIdx,
                                                endModuleIdx)), false);
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

            result.addMarker(new TLAMarkerInformationHolder(project, project.getName(), IMarker.SEVERITY_ERROR, new int[] {
                    -1, -1, -1, -1 }, "Could not find module"));
            break;
        case IParseConstants.PARSED:
            break;
        default:
            throw new RuntimeException("No default expected. Still spec.getStatus() returned a value of "
                    + result.getStatus());
        }
    } // ProcessParsingErrorMsgs

    /**
     * Looks for line and column number in str starting at idx, and returns a 3-element array val with val[0] = the line
     * number and val[1] = the column number, and val[2] the index at the end of the column number. It returns -1 for a
     * number it doesn't find, and may leave val[3] off the end of the array. It works (but of course finds nothing if
     * idx >= str.length(). This is a kludge that assumes that the line number is preceded either by " line " or by
     * "line " that begins the error message, and that the column number is preceded by either " column " or " col ".
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
                val[0] = Integer.parseInt(message.substring(beginIndex, endIndex));
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
                        val[1] = Integer.parseInt(message.substring(beginIndex, endIndex));
                        val[2] = endIndex;
                    } // if (beginIndex < str.length())
                } // if (beginIndex != -1)
            } // if (beginIndex < str.length())
        } // if (beginIndex != -1)
        return val;
    } // findLineAndColumn

}
