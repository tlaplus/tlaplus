// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.drivers;

import tla2sany.configuration.Configuration;
import tla2sany.explorer.Explorer;
import tla2sany.explorer.ExplorerQuitException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.*;
import tla2sany.st.TreeNode;

import util.FileUtil;
import util.ToolIO;
import util.UniqueString;
import util.UsageGenerator;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * This is the main entry point for the TLA+ front end that performa parsing, semantic analysis,
 * and level-checking for a TLA+ spec.
 */

public class SANY {


    /*************************************************************************
     * Version information.                                                   *
     *************************************************************************/

//  The following method for automatically inserting the version date was
//  removed on 20 Jul 2011 by LL because Emacs is no longer being used to
//  edit the source files.

    private static final String modDate = "08 July 2020";
//                lastModified.substring(21, lastModified.indexOf(" at"));
    /***********************************************************************
     * The modification date.                                               *
     ***********************************************************************/

    public static final String version =
            "Version 2.2 created " + modDate;

    private final boolean doParsing = true;
    // true <=> parsing should be done
    //          currently there is no way to turn this off
    /**
     * The SANY.frontEndMain method Processes an entire TLA+ spec
     * that starts in the file named in "filename", including all files
     * it refers to directly or indirectly in EXTENDS or INSTANCE
     * constructs.  "fileName" is relative to the current directory.  It
     * is expected to end with the extension ".tla"; if it does not,
     * then ".tla" is appended before processing it.
     * <p>
     * This method does (1) parsing, (2) semantic analysis, and (3)
     * level-checking, and returns a Specification object, which is the
     * root of the semantic graph of the specification.
     * <p>
     * It also sends progress indications and a text error stream
     * suitable for printing on System.out or System.err to the
     * PrintStream "syserr" (unless "syserr" is null).  The error stream
     * is also saved in Errors objects that are components of the
     * Specification object returned.  The caller may prefer to pass
     * syserr = null, and use the these Errors objects to provide
     * feedback to the human spec-writer in some other way.
     * <p>
     * This method returns a Specification object, even if warnings,
     * errors, or aborts occurred during processing.  (But the
     * Specification may be incomplete, in that not all modules or
     * definitions are processed.)
     * <p>
     * The Specification object returned must be queried by the caller
     * using getErrorLevel() to see what level of problems, if any,
     * occurred during the three phases.  Any value from getErrorLevel()
     * other than 0 is fatal, and the caller should not use the
     * specification object any more.
     * <p>
     * This method throws a FrontEndException if an unexpected runtime
     * error occurs in the FrontEnd.  This exception is NOT thrown for
     * ordinary Warning, Error, or Abort conditions detected during
     * processing--those are reported in the returned specification
     * object, which must be checked as described above.
     */

    public Context context;
    // true <=> semantic analysis should be done
    //          default is true; turned OFF by -S switch
    private boolean doSemanticAnalysis = true;
    // true <=> level checking should be done
    //          no effect if doSemanticAnalysis is false
    //          default is true; turned OFF by -L switch
    private boolean doLevelChecking = true;
    // true <=> control should be transferred to debugger;
    //          default is false; turned ON by -D switch
    private boolean doDebugging = false;
    // true <=> statistics about builtin operator usage 
    //          should be reported
    private boolean doStats = false;
    // true <=> error level should be reported as the tools'
    //          return value
    private boolean doStrictErrorCodes = false;
    private Configuration configuration;

    private BuiltInLevel builtInLevel;

    public SANY() {
    }

    /**
     * Main driver method for maintainers and debuggers of SANY.
     * <p>
     * Calls frontEndMain for each file named on the command line and then,
     * barring errors too severe, calls the Explorer tool with the resulting
     * ExternalModuleTable.
     */
    public static int SANYmain(final String[] args) {
        var sany = new SANY();
        return sany.handleArgs(args);
    }

    public final int frontEndMain(
            final SpecObj spec,
            final String fileName,
            final PrintStream syserr) throws FrontEndException {
        try {
            // **** Initialize the global environment
            frontEndInitialize(spec, syserr);

            // **** Parsing
            if (doParsing) frontEndParse(spec, syserr);

            // **** Semantic analysis and level checking
            if (doSemanticAnalysis) {
                frontEndSemanticAnalysis(spec, syserr, doLevelChecking);
            }
        } catch (final InitException | SemanticException | ParseException ie) {
            return -1;
        } catch (final Exception e) {
            // e.printStackTrace(syserr);
            syserr.println(e);
            throw new FrontEndException(e);
        }
        if (doStrictErrorCodes) {
            return spec.errorLevel;
        } else {
            return 0;
        }
    }

    /**
     * Initialize the all parts of the FrontEnd to handle a new specification.
     */
    public void frontEndInitialize(final SpecObj spec, final PrintStream syserr)
            throws InitException {
        final String fileName = spec.getFileName();
        final Errors initErrors = spec.initErrors;
        try {
            // Read & initialize config file for each specification

            // Set Configuration class to (re)start

            // (Re)parse tables of builtin operators and synonyms into the
            // global context
            configuration = Configuration.load(initErrors);
            context = configuration.context;

            spec.operators = configuration.operators;

            // (Re)read & initialize level data for builtin operators
            builtInLevel = BuiltInLevel.load(context);

            // Print any errors from parsing during initialization phase
            if (!initErrors.isSuccess()) {
                syserr.println("*** Errors during initialization of SANY:\n");
                syserr.print(initErrors);

                // indicate fatal error during first phase
                spec.errorLevel = 1;
                throw new InitException();
            }
        } catch (final Exception e) {
            syserr.println("Unexpected exception during SANY initialization " +
                    fileName + "\n" + e);
            syserr.println("Initialization errors detected before " +
                    "the unexpected exception:\n");
            syserr.print(initErrors);

            // indicate fatal error during first phase
            spec.errorLevel = 1;
            throw new InitException();
        }
    } // frontEndInitialize

    // Parse all of the files referred to by the top-level file in specification
    public void frontEndParse(final SpecObj spec, final PrintStream syserr)
            throws ParseException {
        frontEndParse(spec, syserr, true);
    }

    public void frontEndParse(final SpecObj spec, final PrintStream syserr, final boolean validatePCalTranslation)
            throws ParseException {
        /***********************************************************************
         * Modified on 12 May 2008 by LL to remove "throws AbortException",     *
         * since it catches all exceptions and turns them into                  *
         * ParseExceptions.                                                     *
         ***********************************************************************/
        try {
            // Actual parsing method called from inside loadSpec()
            spec.loadSpec(spec.getFileName(), spec.parseErrors, validatePCalTranslation);// dead code SZ 02. Aug 2009

            if (!spec.parseErrors.isSuccess()) {
                if (syserr != null) syserr.println(spec.parseErrors);

                // indicate fatal error during parsing phase
                spec.errorLevel = 2;
                throw new ParseException();
            }
        }
        // TODO
        catch (final ParseException e) {
            // get here if either the TLAPlusParser.parse() threw a ParseException or spec.ParseErrors was not empty
            throw new ParseException();
        } catch (final Exception e) {
            // Assert.printStack(e);
            Objects.requireNonNull(syserr).println("\nFatal errors while parsing TLA+ spec in file " +
                    spec.getFileName() + "\n");

            syserr.println(e);
            // syserr.println("Parsing errors detected before unexpected exception:\n");
            syserr.print(spec.parseErrors);

            throw new ParseException();
        }
    } //

    public void frontEndSemanticAnalysis(final SpecObj spec,
                                         final PrintStream syserr,
                                         final boolean levelCheck)
            throws SemanticException {
        String moduleStringName;
        TreeNode syntaxTreeRoot;
        final ExternalModuleTable externalModuleTable = spec.getExternalModuleTable();
        ParseUnit parseUnit;
        ModuleNode moduleNode;
        final Errors semanticErrors = spec.semanticErrors;
        final Errors globalContextErrors = context.getErrors();

        try {
            SemanticNode.setErrors(semanticErrors);

            // Go through the semanticAnalysisArrayList, and generate the
            // semantic graph for each external module in it, adding at each
            // iteration what was generated (i.e. <context, node>) to
            // externalModuleTable.  The semanticAnalysisArrayList is ordered
            // so that is A depends on B, then B has a lower index in the
            // ArrayList than A.
            for (int i = 0; i < spec.semanticAnalysisArrayList.size(); i++) {
                moduleStringName = spec.semanticAnalysisArrayList.get(i);

                // if semantic analysis has not already been done on this module
                if (externalModuleTable.getContext(UniqueString.uniqueStringOf(moduleStringName)) == null) {
                    parseUnit = spec.parseUnitContext.get(moduleStringName);

                    // get reference to the syntax tree for the module
                    syntaxTreeRoot = parseUnit.getParseTree();

                    // Generate semantic graph for the entire external module
                    syserr.println("Semantic processing of module " + moduleStringName);
                    // create new Generator object
                    final Generator gen = new Generator(configuration, externalModuleTable, semanticErrors);

                    // Perform semantic analysis and create semantic graph for one external module here
                    moduleNode = gen.generate(Objects.requireNonNull(syntaxTreeRoot));

                    // Set the isStandard field of the moduleNode.
                    // Added by LL on 24 July 2013
                    Objects.requireNonNull(moduleNode).setStandard(spec.getResolver().isStandardModule(moduleStringName));

                    // Put the semantic graph and related info for moduleNode into the module table
                    externalModuleTable.put(UniqueString.uniqueStringOf(moduleStringName),
                            gen.getSymbolTable().getExternalContext(),
                            moduleNode);

                    // Level check if semantic analysis succeeded and levelCheck is true.
                    if (semanticErrors.isSuccess() && levelCheck) {
                        moduleNode.levelCheck(1);
                    }

                    // Indicate in the externalModuleTable that the last module
                    // analyzed is the root ModuleNode
                    if (i == spec.semanticAnalysisArrayList.size() - 1) {
                        externalModuleTable.setRootModule(moduleNode);
                    }

                    // Print error and warning messages for this module
                    if (globalContextErrors.getNumMessages() > 0) {
                        syserr.println("Semantic errors in global context:\n");
                        syserr.print("\n" + globalContextErrors);
                        // indicate fatal error parsing builtin operator tables
                        spec.errorLevel = 3;
                        /**
                         *  We believe that globalContextErrors is pointing to a global list
                         *  of context errors
                         *  that keeps being added to.  By setting spec.globalContextErrors
                         *  to its value, we ensure that when we finish, spec.globalContextErrors
                         *  contains the ArrayList of all the globalContextErrors.
                         */
                        spec.setGlobalContextErrors(globalContextErrors);
                    }

                    if (semanticErrors.getNumMessages() > 0) {
                        syserr.println("Semantic errors:\n\n" + semanticErrors);
                        // indicate fatal error during semantic analysis or level-checking
                        if (semanticErrors.getNumAbortsAndErrors() > 0) {
                            spec.errorLevel = 4;
                        } // end if
                    } // end if
                } // end if
            } // end while
        } catch (final AbortException e) {
            syserr.println("Fatal errors in semantic processing of TLA spec " +
                    spec.getFileName() + "\n" + e.getMessage() +
                    "\nStack trace for exception:\n");
            e.printStackTrace(syserr);

            if (globalContextErrors.getNumMessages() > 0) {
                syserr.println("Semantic errors in global context detected before the unexpected exception:\n");
                syserr.print("\n" + globalContextErrors);

                // indicate fatal error parsing builtin operator tables
                spec.errorLevel = 3;
            }

            if (semanticErrors.getNumMessages() > 0) {
                syserr.println("Semantic errors detected before the unexpected exception:\n");
                syserr.print("\n" + semanticErrors);

                // indicate fatal error during semantic analysis or level-checking
                if (semanticErrors.getNumAbortsAndErrors() > 0) {
                    spec.errorLevel = 4;
                }
            }
            throw new SemanticException();
        }
    }

    private static void printUsage()
    {
        final List<List<UsageGenerator.Argument>> commandVariants = new ArrayList<>();
        final List<UsageGenerator.Argument> variant = new ArrayList<>();
        variant.add(new UsageGenerator.Argument(
                "-s", "Turns off semantic analysis", true));
        commandVariants.add(variant);
        variant.add(new UsageGenerator.Argument(
                "-l", "Turns off level checking. Level checking won't be\n" +
                "used, if the semantic analysis is disabled. ", true));
        variant.add(new UsageGenerator.Argument(
                "-stat", "Turns off reporting statistics about builtin operator\n" +
                "usage." , true));
        variant.add(new UsageGenerator.Argument(
                "-error-codes", "If enabled, error level will be reported as the tools'\n" +
                "return value." , true));
        commandVariants.add(variant);
        final List<String> tips = new ArrayList<>();
        UsageGenerator.displayUsage(
                ToolIO.out, "SANY", version,
                "provides parsing, semantic analysis, and level-checking for a TLA+ spec",
                """
                        SANY is a parser and syntax checker for TLA+ specifications.
                        It catches parsing errors and some "semantic" errors such as
                        priming an expression containing primed variables.""",
                commandVariants, tips, ' ');
    }


    /**
     * This method should print statistics about the specification
     * It is obviously not finished.
     */
    public final void frontEndStatistics(final SpecObj spec) {

    }

    public int handleArgs(final String[] args) {
        int i;
        // Parse and process the command line switches, which are
        // distinguished by the fact that they begin with a '-' character.
        // Once the first command line element that is NOT a switch is
        // encountered, the rest are presumed to be file names.
        for (i = 0; (i < args.length) && (args[i].charAt(0) == '-'); i++) {
            if (args[i].equals("-S") || args[i].equals("-s"))
                doSemanticAnalysis = !doSemanticAnalysis;
            else if (args[i].equals("-L") || args[i].equals("-l"))
                doLevelChecking = !doLevelChecking;
            else if (args[i].equals("-D") || args[i].equals("-d"))
                doDebugging = !doDebugging;
            else if (args[i].equals("-STAT") || args[i].equals("-stat"))
                doStats = !doStats;
            else if (args[i].equalsIgnoreCase("-error-codes"))
                doStrictErrorCodes = true;
            else if (args[i].equalsIgnoreCase("-help")) {
                printUsage();
                System.exit(0);
            } else {
                ToolIO.out.println("Command-line error: " + args[i]);
                ToolIO.out.println("Use -help option for more information.");
                System.exit(-1);
            }
        }

        // After the termination of the previous loop, the remaining
        // elements on the command line must be file names for specifications.

        // For each file named on the command line (i.e. in the args
        // array) (re)initialize the entire system and process that file
        // as the root of a new specification.
        for (; i < args.length; i++) {
            // continue the loop where the last one left off
            // Print documentation line on System.out
            ToolIO.out.println("\n****** SANY2 " + version + "\n");

            // Get next file name from command line; then parse,
            // semantically analyze, and level check the spec started in
            // file Filename leaving the result (normally) in Specification
            // spec.
            final SpecObj spec = new SpecObj(args[i], null);
            // check if file exists
            if (FileUtil.namedInputStreamCanBeCreated(args[i], spec.getResolver())) {
                try {
                    final int ret = frontEndMain(spec, args[i], ToolIO.out);
                    if (ret != 0) {
                        return ret;
                    }
                } catch (final FrontEndException fe) {
                    // For debugging
                    fe.printStackTrace();
                    ToolIO.out.println(fe);
                    return -1;
                }

                // Compile operator usage stats
                if (doStats) frontEndStatistics(spec);

                if (doDebugging) {
                    // Run the Semantic Graph Exploration tool
                    final Explorer explorer = new Explorer(spec.getExternalModuleTable());
                    try {
                        explorer.main(args);
                    } catch (final ExplorerQuitException e) { /*do nothing*/ }
                }
            } else {
                ToolIO.out.println("Cannot find the specified file " + args[i] + ".");
                return -1;
            }
        }

        return 0;
    }
}
