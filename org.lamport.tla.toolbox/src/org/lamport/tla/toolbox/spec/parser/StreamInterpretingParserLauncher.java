package org.lamport.tla.toolbox.spec.parser;

import java.io.File;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.Vector;

import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.problem.Problem;
import org.lamport.tla.toolbox.ui.handler.ParseHandler;
import org.lamport.tla.toolbox.util.RCPNameToFileIStream;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.drivers.InitException;
import tla2sany.drivers.SANY;
import tla2sany.drivers.SemanticException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import util.ToolIO;
import util.UniqueString;

/**
 * This parser launcher starts SANY and uses SANY's console output to find errors
 * 
 * @author zambrovski
 * @version $Id$
 */
public class StreamInterpretingParserLauncher implements IParserLauncher
{
    private Errors parseErrors = null;
    private Errors semanticErrors = null;

    /*
     * (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.parser.IParserLauncher#parseSpecification(toolbox.spec.Spec)
     */
    public int parseSpecification(Spec specification)
    {

        ToolIO.setUserDir(ResourceHelper.getParentDir(specification.getRootFilename()));

        // call the parsing
        int status = parseMainModule(true, specification.getRootFilename());
        // System.out.println("Parsing Status: " + status);

        // set the status back into the spec
        specification.setStatus(status);

        // reset problems from previous run
        specification.getParseProblems().reset();

        // store errors inside the specification
        processParsingErrors(specification);

        return status;
    }

    /**
     * Calls SANY, that parses the root module. <br>
     * <b>Note:</b> This method fills the error objects {@link ParseHandler#parseErrors} and
     * {@link ParseHandler#semanticErrors}. Call {@link ParseHandler#processParsingErrors(Spec)} to store this
     * information in the specification handle
     * 
     * @param doSemanticAnalysis
     *            if true, the semantical phase will be started
     * @param rootFilename
     *            filename of the root module
     * @return status of parsing, one of the {@link IParseConstants} constants
     */
    private int parseMainModule(boolean doSemanticAnalysis, String rootFilename)
    {
        // clean the results of previos parsing
        cleanUp();

        // one of the Spec constants
        int specStatus = 0;

        // The parsing methods take a PrintStream on which they print out some (but hardly all) error messages.
        // They're called with this one.
        PrintStream outputStr = ToolIO.err;

        // Initialize the module variables
        SpecObj moduleSpec = new SpecObj(ResourceHelper.getModuleName(rootFilename), new RCPNameToFileIStream(null));

        // Reset the tool output messages. *
        ToolIO.reset();
        ToolIO.setMode(ToolIO.TOOL);

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
            return specStatus;
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
            if (parseUnit.getNis() != null)
            {
                File sourceFile = parseUnit.getNis().sourceFile();
                if (sourceFile != null)
                {
                    absoluteFileName = sourceFile.getAbsolutePath();
                } // if (sf != null)
            } // if (nis != null)

            if (absoluteFileName == null)
            {
                // TODO
                // GUI.ReportBug(null,
                // "Bug: Spec.ParseMainModule:1730");
            }

            // create module holder
            Module holder = new Module(absoluteFileName);

            // semantic module only available if no semantic errors found
            if (specStatus > IParseConstants.SEMANTIC_ERROR)
            {
                ExternalModuleTable.ExternalModuleTableEntry emt = (ExternalModuleTable.ExternalModuleTableEntry) moduleSpec
                        .getExternalModuleTable().moduleHashTable.get(UniqueString.uniqueStringOf(holder
                        .getModuleName()));
                if (emt != null)
                {
                    holder.setNode(emt.getModuleNode());
                }
            }

            if (holder.getModuleName().equals(ResourceHelper.getModuleName(rootFilename)))
            {
                rootModuleFound = true;
            }

            if (holder.isStandardModule())
            {
                standardModules.addElement(holder);
            } else
            {
                userModules.addElement(holder);
            }

        } // while

        if (!rootModuleFound)
        {
            specStatus = IParseConstants.COULD_NOT_FIND_MODULE;
        }

        return specStatus;
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
    private void processParsingErrors(Spec spec)
    {

        switch (spec.getStatus()) {
        /* ------------------ SYNTAX ERRORS --------------------- */
        case IParseConstants.SYNTAX_ERROR: {

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
            String[] output = ToolIO.getAllMessages();
            int nextMsg = 0;

            Problem holder = new Problem(Problem.ERROR);
            // Set module name and leave nextMsg the index of the error message.
            while ((nextMsg < output.length) && (output[nextMsg].indexOf("Parsing module") != -1))
            {
                nextMsg++;
            }
            if ((nextMsg != 0) && (nextMsg != output.length))
            {
                String str = output[nextMsg - 1];
                int pmi = str.indexOf("Parsing module") + 15;
                holder.location.moduleName = str.substring(pmi, str.indexOf(" ", pmi + 1));
            } // if
            else
            {
                // TODO
                throw new RuntimeException("Console parsing BUG");
                // GUI.ReportBug(null,
                // "Bug Spec.ProcessParsingErrorMessages:1869.  "
                // + "Can't find module name") ;
            } // else

            // Get any line numbers and get the message.
            String errMsg = output[nextMsg];
            if ((errMsg.indexOf("Lexical error") != -1) || (errMsg.indexOf("***Parse Error***") != -1))
            {
                // This is a meaningful error message and should have at least
                // one line, column number.
                int[] val = findLineAndColumn(0, errMsg);
                holder.location.beginLine = val[0];
                holder.location.beginColumn = val[1];
                val = findLineAndColumn(val[2], errMsg);

                // Set err.endLine, err.endColumn if position val[0], val[1] is
                // after err.beginLine, err.beginColumn.
                if ((val[0] > holder.location.beginLine)
                        || ((val[0] == holder.location.beginLine) && (val[1] >= holder.location.beginColumn)))
                {
                    holder.location.endLine = val[0];
                    holder.location.endColumn = val[1];
                }
                holder.message = errMsg;
            } // if
            else
            {
                // This is not a meaningful error message; get the message from
                // the abort in parseErrors
                if (parseErrors != null)
                {
                    String[] aborts = parseErrors.getAborts();
                    if (aborts.length > 0)
                    {
                        holder.message = aborts[0];
                    }
                }
                // Unless this is the one abort in which err.moduleName can be
                // computed from the error messages, reset it to "".
                if (holder.message.indexOf("does not match the name") == -1)
                {
                    holder.location.moduleName = "";
                }
            } // else

            // add the error to the spec
            spec.getParseProblems().addProblem(holder);

            break;
        }
            /* ------------------ SEMANTIC ERRORS AND WARNINGS --------------------- */
        case IParseConstants.SEMANTIC_ERROR:
        case IParseConstants.SEMANTIC_WARNING: {
            // There were semantic errors or warnings; set semanticGUIErrors.
            if (semanticErrors == null)
            {
                // TODO
                // GUI.ReportBug(window,
                // "Bug Spec.ProcessParsingErrorMsgs.1418:\n" +
                // "Semantic error detected but no error message found.");
            }

            String[][] errors = { semanticErrors.getAborts(), semanticErrors.getErrors(), semanticErrors.getWarnings() };
            int[] holderType = { Problem.ABORT, Problem.ERROR, Problem.WARNING };

            for (int j = 0; j < 3; j++)
            {
                for (int i = 0; i < errors[j].length; i++)
                {
                    // assumes that the holderType array holds the types corresponding to the way errors[][]
                    // constructed
                    Problem holder = new Problem(holderType[j]);
                    // store the message text
                    holder.message = errors[j][i];

                    // Get pair of line, column numbers
                    int[] val = findLineAndColumn(0, holder.message);
                    holder.location.beginLine = val[0];
                    holder.location.beginColumn = val[1];
                    val = findLineAndColumn(val[2], holder.message);
                    if ((val[0] > holder.location.beginLine)
                            || ((val[0] == holder.location.beginLine) && (val[1] >= holder.location.beginColumn)))
                    {
                        holder.location.endLine = val[0];
                        holder.location.endColumn = val[1];
                    }

                    // Get module name. We use the fact that errors and warnings are always generated with the
                    // module
                    // indicated by " module Name\n". *
                    int beginModuleIdx = holder.message.indexOf(" module ");
                    if (beginModuleIdx != -1)
                    {
                        beginModuleIdx = beginModuleIdx + " module ".length();
                        int endModuleIdx = holder.message.indexOf("\n", beginModuleIdx);
                        if (endModuleIdx != -1)
                        {
                            holder.location.moduleName = holder.message.substring(beginModuleIdx, endModuleIdx);
                        }
                    }
                    // add error to the spec
                    spec.getParseProblems().addProblem(holder);
                }
            }// for i, for j

            break;
        }

        }

        cleanUp();
    } // ProcessParsingErrorMsgs

    public void cleanUp()
    {
        // cleanup the
        this.parseErrors = null;
        this.semanticErrors = null;
    }

    /**
     * Looks for line and column number in str starting at idx, and returns a 3-element array val with val[0] = the line
     * number and val[1] = the column number, and val[2] the index at the end of the column number. It returns -1 for a
     * number it doesn't find, and may leave val[3] off the end of the array. It works (but of course finds nothing if
     * idx >= str.length(). This is a kludge that assumes that the line number is preceded either by " line " or by
     * "line " that begins the error message, and that the column number is preceded by either " column " or " col ".
     */
    static final int[] findLineAndColumn(final int idx, final String message)
    {
        int[] val = /* new int[3] */{ -1, -1, message.length() };

        /***********************************************************************
         * Search for either " line " or "line " starting at idx. *
         ***********************************************************************/
        int beginIndex = message.indexOf("line ", idx);
        int offset = 5;
        if (beginIndex != idx)
        {
            beginIndex = -1;
        }
        ;
        if (beginIndex == -1)
        {
            beginIndex = message.indexOf(" line ", idx);
            offset = 6;
        }
        ;
        if (beginIndex != -1)
        {
            /***************************************************************
             * Found " line ". Set beginIndex, endLineIndex to the * beginning and past the end of the line number. *
             ***************************************************************/
            beginIndex = beginIndex + offset;
            while ((beginIndex < message.length()) && !Character.isDigit(message.charAt(beginIndex)))
            {
                beginIndex++;
            }
            ; // while
            int endIndex = beginIndex + 1;
            while ((endIndex < message.length()) && Character.isDigit(message.charAt(endIndex)))
            {
                endIndex++;
            }
            ;
            if (beginIndex < message.length())
            {
                /*******************************************************************
                 * Valid values of beginIndex and endIndex, so set val[0] and look * for the column number. *
                 *******************************************************************/
                val[0] = Integer.parseInt(message.substring(beginIndex, endIndex));
                beginIndex = message.indexOf(" column ", endIndex);
                int colOffset = 0; // to keep compiler happy.
                if (beginIndex != -1)
                {
                    colOffset = 8;
                }
                ;
                int otherIndex = message.indexOf(" col ", endIndex);
                if ((otherIndex != -1) && ((beginIndex == -1) || (otherIndex < beginIndex)))
                {
                    beginIndex = otherIndex;
                    colOffset = 5;
                } // else
                if (beginIndex != -1)
                {
                    /*****************************************************************
                     * Found either " column " or " col ". Set beginIndex, endIndex * to the beginning and past the end
                     * of the line number. *
                     *****************************************************************/
                    beginIndex = beginIndex + colOffset;
                    while ((beginIndex < message.length()) && !Character.isDigit(message.charAt(beginIndex)))
                    {
                        beginIndex++;
                    }
                    ; // while
                    endIndex = beginIndex + 1;
                    while ((endIndex < message.length()) && Character.isDigit(message.charAt(endIndex)))
                    {
                        endIndex++;
                    }
                    ;
                    if (beginIndex < message.length())
                    {
                        /***************************************************************
                         * Valid values of beginIndex and endIndex, so set val[1] and * val[2]. *
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
