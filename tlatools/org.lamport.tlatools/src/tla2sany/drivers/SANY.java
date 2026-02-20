

// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.drivers;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import tla2sany.explorer.Explorer;
import tla2sany.explorer.ExplorerQuitException;
import tla2sany.linter.Linter;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.OutErrSanyOutput;
import tla2sany.output.SanyOutput;
import tla2sany.output.SimpleSanyOutput;
import tla2sany.parser.ParseException;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Context;
import tla2sany.semantic.Errors;
import tla2sany.semantic.Errors.ErrorDetails;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.Generator;
import tla2sany.semantic.ModuleNode;
import tla2sany.st.TreeNode;
import util.FileUtil;
import util.ToolIO;
import util.UniqueString;
import util.UsageGenerator;

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
//
//  private static String lastModified = 
//    /***********************************************************************
//    * The following string is inserted by an Emacs macro when a new        *
//    * version is saved.                                                    *
//    ***********************************************************************/
//    "last modified on Tue  10 February 2011 at 11:49:54 PST by lamport";

  private static String modDate = "08 July 2020";
//                lastModified.substring(21, lastModified.indexOf(" at"));
    /***********************************************************************
    * The modification date.                                               *
    ***********************************************************************/

  public static String version = 
    "Version 2.2 created " + modDate ; 

  private static boolean doSemanticAnalysis = true;  
    // true <=> semantic analysis should be done
    //          default is true; turned OFF by -S switch

  private static boolean doLevelChecking    = true;  
    // true <=> level checking should be done
    //          no effect if doSemanticAnalysis is false
    //          default is true; turned OFF by -L switch

  private static boolean doLinting = true;  
  // true <=> linting should be done
  //          default is true; turned OFF by -G switch

  private static boolean doDebugging        = false; 
    // true <=> control should be transferred to debugger;
    //          default is false; turned ON by -D switch

  private static boolean doStrictErrorCodes   = false;
    // true <=> error level should be reported as the tools'
    //          return value

  /**
   * The default setting of whether to validate the root module's PlusCal
   * translation and warn if it is out of sync.
   */
  private static final boolean doValidatePCalTranslationDefault = true;

  /**
   * Use {@link SANY#frontEndMain(SpecObj, String, SanyOutput, SanySettings)}
   * instead for greater control of output and settings. This method will
   * print all human-readable log messages to the provided syserr parameter.
   * The syserr parameter cannot be null.
   */
  @Deprecated
  public static final int frontEndMain(
                             SpecObj spec, 
                             String fileName, 
                             PrintStream syserr) throws FrontEndException {
    return frontEndMain(spec, fileName, new SimpleSanyOutput(syserr, LogLevel.INFO));
  }

  /**
   * Use {@link SANY#frontEndMain(SpecObj, String, SanyOutput, SanySettings)}
   * instead for greater control of output and settings.
   */
  @Deprecated
  public static final int frontEndMain(
                             SpecObj spec, 
                             String fileName, 
                             SanyOutput out) throws FrontEndException {
    SanySettings settings = new SanySettings(
        doStrictErrorCodes,
        doSemanticAnalysis,
        doLevelChecking,
        doLinting,
        doValidatePCalTranslationDefault
      );
    return parse(spec, fileName, out, settings);
  }

  /**
   * This method processes an entire TLA+ spec that starts in the file named
   * in the "fileName" parameter, including all files it refers to directly
   * or indirectly in EXTENDS or INSTANCE constructs. "fileName" is relative
   * to the current working directory. It is expected to end with the
   * extension ".tla"; if it does not, then ".tla" is appended.
   *
   * This method does (1) syntax parsing, (2) semantic analysis, (3) level-
   * checking, and (4) linting; it modifies the spec object in place to form
   * the root of the semantic graph of the specification. A nonzero code is
   * returned in case of error and when {@link SanySettings#doStrictErrorCodes}
   * is set (which it always will be for external users). The later parser
   * phases can be optionally disabled using the {@link SanySetting} object.
   *
   * This method sends progress indications and other log messages to the
   * {@link SanyOutput} parameter. Errors and warnings (along with machine-
   * readable metadata) are furthermore saved to an {@link Errors} instance
   * in the spec object for later processing. If no human-readable log output
   * is desired, a {@link tla2sany.output.SilentSanyOutput} instance should
   * be provided.
   *
   * The spec object returned must be queried by the caller using
   * {@link SpecObj#getErrorLevel()} to see what level of problems, if any,
   * occurred during the parsing phases. Any value other than 0 is fatal, and
   * the caller should not use the spec object any more. To see the actual
   * list of failures tagged with an {@link tla2sany.semantic.ErrorCode},
   * call {@link SpecObj#getParseErrors()} and {@link SpecObj#getSemanticErrors()}.
   *
   * This method throws a {@link FrontEndException} if an unexpected runtime
   * error occurs during parsing. This exception is NOT thrown for ordinary
   * {@link tla2sany.semantic.ErrorCode.ErrorLevel.WARNING} or
   * {@link tla2sany.semantic.ErrorCode.ErrorLevel.ERROR} occurrences, which
   * are reported through the {@link Errors} instances as explained above.
   */
  public static final int parse(
                             SpecObj spec, 
                             String fileName, 
                             SanyOutput out,
                             SanySettings settings) throws FrontEndException {
    try {
      // **** Initialize the global environment
      frontEndInitialize();
    
      // **** Parsing 
      frontEndParse(spec, out, settings.validatePCalTranslation);
    
      // **** Semantic analysis and level checking
      if (settings.doSemanticAnalysis) 
            {frontEndSemanticAnalysis(spec, out, settings.doLevelChecking);} ;

      // **** Linting
      if (settings.doLinting) 
            {frontEndLinting(spec, out); } ;

    }
    catch (ParseException pe) {
      return -1;
    }
    catch (SemanticException se) {
      return -1;
    }
    catch (Exception e) {
      out.log(LogLevel.ERROR, e.toString());
      throw new FrontEndException(e);
    }
    if (settings.doStrictErrorCodes) {
      return spec.errorLevel;
    } else {
      return 0;
    }
  }

  /** 
   * Initialize the all parts of the FrontEnd to handle a new specification.
   */
  public static void frontEndInitialize() {
    Context.reInit();
  } // frontEndInitialize

  /**
   * Use {@link SANY#frontEndParse(SpecObj, SanyOutput)} instead for greater
   * control of output.
   */
  @Deprecated
  public static void frontEndParse(SpecObj spec, PrintStream syserr)
    throws ParseException {
    frontEndParse(spec, new SimpleSanyOutput(syserr, LogLevel.INFO));
  }

  // Parse all of the files referred to by the top-level file in specification
  public static void frontEndParse(SpecObj spec, SanyOutput out) 
  throws ParseException {
	  frontEndParse(spec, out, true);
  }

  /**
   * Use {@link SANY#frontEndParse(SpecObj, SanyOutput, boolean)} instead for greater
   * control of output.
   */
  @Deprecated
  public static void frontEndParse(SpecObj spec, PrintStream sysErr, boolean validatePCalTranslation)
    throws ParseException {
    frontEndParse(spec, new SimpleSanyOutput(sysErr, LogLevel.INFO), validatePCalTranslation);
  }

  public static void frontEndParse(SpecObj spec, SanyOutput out, boolean validatePCalTranslation) 
  throws ParseException {
      /***********************************************************************
       * Modified on 12 May 2008 by LL to remove "throws AbortException",     *
       * since it catches all exceptions and turns them into                  *
       * ParseExceptions.                                                     *
       ***********************************************************************/
      try 
      {
          // Actual parsing method called from inside loadSpec()
          spec.loadSpec(spec.getFileName(), spec.parseErrors, validatePCalTranslation, out);

          List<ErrorDetails> warnings = spec.parseErrors.getWarningDetails();
          if (!warnings.isEmpty()) {
            out.log(LogLevel.WARNING, "Warnings (%d) during syntax parsing of %s:\n\n", warnings.size(), spec.getFileName());
            for (ErrorDetails warning : warnings) {
              out.log(LogLevel.WARNING, "%s\n\n\n", warning);
            }
          }

          if (!spec.parseErrors.isSuccess()) 
          {
              out.log(LogLevel.ERROR, spec.parseErrors.toString());
              // indicate fatal error during parsing phase
              spec.errorLevel = 2;
              throw new ParseException(); 
          }
      }
      // TODO
      catch (ParseException e) 
      {
          // get here if either the TLAPlusParser.parse() threw a ParseException or spec.ParseErrors was not empty
          spec.errorLevel = 2;
          throw new ParseException();
      }
      catch (Exception e) 
      {
          spec.errorLevel = 2;
          out.log(LogLevel.ERROR, "\nFatal errors while parsing TLA+ spec in file %s\n", spec.getFileName());
          out.log(LogLevel.ERROR, e.toString());
          out.log(LogLevel.ERROR, spec.parseErrors.toString());
          throw new ParseException();
      }
      return;
  } //

  /**
   * Use {@link SANY#frontEndSemanticAnalysis(SpecObj, SanyOutput, boolean)}
   * for greater control over output.
   */
  @Deprecated
  public static void frontEndSemanticAnalysis(SpecObj spec,
                                              PrintStream syserr,
                                              boolean levelCheck) 
  throws SemanticException {
    frontEndSemanticAnalysis(spec, new SimpleSanyOutput(syserr, LogLevel.INFO), levelCheck);
  }

  public static void frontEndSemanticAnalysis(SpecObj spec,
                                              SanyOutput out,
                                              boolean levelCheck) 
  throws SemanticException {
    String      moduleStringName;
    TreeNode    syntaxTreeRoot;
    ExternalModuleTable externalModuleTable = spec.getExternalModuleTable();
    ParseUnit   parseUnit;
    ModuleNode  moduleNode = null;
    Errors      semanticErrors = spec.semanticErrors;

    try {
      // Go through the semanticAnalysisVector, and generate the
      // semantic graph for each external module in it, adding at each
      // iteration what was generated (i.e. <context, node>) to
      // externalModuleTable.  The semanticAnalysisVector is ordered
      // so that is A depends on B, then B has a lower index in the
      // Vector than A.
      for (int i = 0; i < spec.semanticAnalysisVector.size(); i++) {
        moduleStringName = (String)spec.semanticAnalysisVector.elementAt(i);  

        // if semantic analysis has not already been done on this module
        if (externalModuleTable.getContext( UniqueString.uniqueStringOf( moduleStringName)) == null ) {
          parseUnit = (ParseUnit)spec.parseUnitContext.get(moduleStringName);;
      
          // get reference to the syntax tree for the module
          syntaxTreeRoot = parseUnit.getParseTree();

          /*
          // Debugging
          // Print the concrete syntax tree for this ExternalModuleTableEntry
          // Printing is done without the user's request, because if 
          // an abort occurs during semantic processing, we want to be able
          // to look at the syntax tree for a clue.
          if (syserr != null) {
            syserr.println("\n*** Concrete Syntax Tree for Module " + moduleStringName);
          }
          syntaxTreeRoot.printST(0);   // Use zero indentation
          if (syserr != null) {
            syserr.println("\n*** End of concrete syntax tree for Module " + moduleStringName);
          }
          */
 
          // Generate semantic graph for the entire external module
          out.log(LogLevel.INFO, "Semantic processing of module %s", moduleStringName);
          // create new Generator object
          Generator gen = new Generator(externalModuleTable, semanticErrors);
    
          // Perform semantic analysis and create semantic graph for one external module here
          moduleNode = gen.generate(syntaxTreeRoot);    
                      
          // Set the isStandard field of the moduleNode.
          // Added by LL on 24 July 2013
          moduleNode.setStandard(spec.getResolver().isStandardModule(moduleStringName)) ;
          
          // Put the semantic graph and related info for moduleNode into the module table
          externalModuleTable.put(UniqueString.uniqueStringOf(moduleStringName), 
                                  gen.getSymbolTable().getExternalContext(),
                                  moduleNode);
  
          // Level check if semantic analysis succeeded and levelCheck is true.
          if (moduleNode != null && semanticErrors.isSuccess() && levelCheck ) {
            moduleNode.levelCheck(semanticErrors);
          }

          // Indicate in the externalModuleTable that the last module
          // analyzed is the root ModuleNode
          if (i == spec.semanticAnalysisVector.size()-1) { 
            externalModuleTable.setRootModule( moduleNode ); 
          }

          if (semanticErrors.getNumMessages() > 0) {
            // TODO: split warnings & errors out into appropriate log level
            out.log(LogLevel.ERROR, "Semantic errors:\n\n%s", semanticErrors);

            // indicate fatal error during semantic analysis or level-checking
            if ( semanticErrors.getNumErrors() > 0 ) {
              spec.errorLevel = 4;
            } // end if
          } // end if
        } // end if
      } // end while
    }
    catch (AbortException e) {
      out.log(
          LogLevel.ERROR,
          "Fatal errors in semantic processing of TLA spec %s\n%s\nStack trace for exception:\n",
          spec.getFileName(),
          e.getMessage()
      );
      e.printStackTrace(out.getStream(LogLevel.ERROR));
  
      if (semanticErrors.getNumMessages() > 0) {
        out.log(
            LogLevel.ERROR,
            "Semantic errors detected before the unexpected exception:\n\n%s",
            semanticErrors
        );
        
        // indicate fatal error during semantic analysis or level-checking
        if ( semanticErrors.getNumErrors() > 0 ) { 
          spec.errorLevel = 4;
        }
      }
      throw new SemanticException(e);
    }
    return;
  }

	public static void frontEndLinting(final SpecObj spec, final SanyOutput out) {
		final ExternalModuleTable externalModuleTable = spec.getExternalModuleTable();
		final Errors semanticErrors = spec.semanticErrors;

		// If the semantic analysis was successful, run linting on all non-standard
		// modules.
		final Linter linter = new Linter();
		for (ModuleNode module : externalModuleTable.getModuleNodes()) {
			if (module.isStandardModule()) {
				continue; // skip standard modules
			}
			out.log(LogLevel.INFO, "Linting of module %s", module.getName());
			linter.lint(module, externalModuleTable, semanticErrors);
		}
	}

  private static void printUsage()
  {
      final List<List<UsageGenerator.Argument>> commandVariants = new ArrayList<>();
      final List<UsageGenerator.Argument> variant = new ArrayList<>();
      variant.add(new UsageGenerator.Argument(
          "-s", "Turns off semantic analysis and level-checking.", true));
      variant.add(new UsageGenerator.Argument(
          "-l", "Turns off level-checking.", true));
      variant.add(new UsageGenerator.Argument(
          "-error-codes", "Return a descriptive exit code in case of error.\n\n" +
          "'2' Error during parsing.\n" +
          "'4' Error during semantic analysis or level-checking.", true));
      variant.add(new UsageGenerator.Argument(
          "-d", "Opens the semantic graph explorer prompt. The prompt accepts the following commands:\n" +
          "'cst' Prints out the concrete syntax tree.\n" +
          "'dot' Emits the semantic graph to a ModuleName.dot file in the DOT graph" +
          " description language.\n" +
          "'mt'  Prints the module table, a list of all imported modules and their" +
          " top-level definitions.\n" +
          "'mt*' Prints the extended module table including built-in operator definitions.\n\n" +
          "Optionally, skip the prompt and run a command directly by appending it like" +
          " 'SANY -d ModuleName.tla cst'", true));
      variant.add(new UsageGenerator.Argument(
          "FILE...", "1 or more files" , false));
      commandVariants.add(variant);
      final List<String> tips = new ArrayList<String>();
      UsageGenerator.displayUsage(
          ToolIO.out, "SANY", version,
    	  "provides parsing, semantic analysis, and level-checking for a TLA+ spec",
          "SANY is a parser and syntax checker for TLA+ specifications.\n" +
          "It catches parsing errors and some \"semantic\" errors such as\n" +
          "priming an expression containing primed variables.",
    	  commandVariants, tips, ' ');
  }

  /**
   * Main driver method for maintainers and debuggers of SANY.
   * 
   * Calls frontEndMain for each file named on the command line and then, 
   * barring errors too severe, calls the Explorer tool with the resulting 
   * ExternalModuleTable.
   */
  public static void SANYmain(String args[]) {
    try {
    	SANYmain0(args);
    } catch (SANYExitException e) {
    	System.exit(e.getExitCode());
    }
  }

  public static void SANYmain0(String args[]) throws SANYExitException {
    if (args.length == 0) {
      printUsage();
      throw new SANYExitException(-1, "No arguments provided");
    }
    int i;
    // Parse and process the command line switches, which are
    // distinguished by the fact that they begin with a '-' character.
    // Once the first command line element that is NOT a switch is
    // encountered, the rest are presumed to be file names.
    for (i = 0; (i < args.length) &&  (args[i].charAt(0) == '-'); i++) {
      if (args[i].equals("-S") || args[i].equals("-s")) 
          doSemanticAnalysis = !doSemanticAnalysis;
      else if (args[i].equals("-L") || args[i].equals("-l")) 
           doLevelChecking    = !doLevelChecking;
      else if (args[i].equals("-G") || args[i].equals("-g")) 
          doLinting    = !doLinting;
      else if (args[i].equals("-D") || args[i].equals("-d")) 
           doDebugging        = !doDebugging;
      else if (args[i].equals("-STAT") || args[i].equals("-stat")) {
           // The stat argument is still accepted to avoid breaking existing 
           // scripts but is ignored.
      }
      else if (args[i].toLowerCase().equals("-error-codes"))
           doStrictErrorCodes = true;
      else if (args[i].toLowerCase().equals("-help")) {
           printUsage();
           return;
      } else {
           ToolIO.out.println("Invalid option: " + args[i]);
           ToolIO.out.println("Try 'SANY -help' for more information.");
           throw new SANYExitException(-1, "Invalid option: " + args[i]);
      }
    }

    if (i == args.length) {
      ToolIO.out.println("At least 1 filename is required.");
      ToolIO.out.println("Try 'SANY -help' for more information.");
      throw new SANYExitException(-1, "No filename provided");
    }

    final SanyOutput out = new OutErrSanyOutput(
        ToolIO.out,
        Boolean.getBoolean(SANY.class.getName() + ".errors2stderr") ? ToolIO.err : ToolIO.out,
        LogLevel.INFO,
        LogLevel.ERROR
    );

    // After the termination of the previous loop, the remaining
    // elements on the command line must be file names for specifications.

    // For each file named on the command line (i.e. in the args
    // array) (re)initialize the entire system and process that file
    // as the root of a new specification.
    for ( ; i < args.length; i++) {
      // continue the loop where the last one left off
      // Print documentation line on System.out
      out.log(LogLevel.INFO, "\n****** SANY2 %s\n", version);

      // Get next file name from command line; then parse,
      // semantically analyze, and level check the spec started in
      // file Filename leaving the result (normally) in Specification
      // spec.
      SpecObj spec = new SpecObj(args[i], null);
      // check if file exists
      if (FileUtil.createNamedInputStream(args[i], spec.getResolver()) != null) 
      {
          try {
              int ret = frontEndMain(spec, args[i], out);
			  if (ret != 0) {
            	  throw new SANYExitException(ret, "Frontend returned error code: " + ret);
              }
            }
            catch (FrontEndException fe) {
              // For debugging
              fe.printStackTrace();   
              out.log(LogLevel.ERROR, fe.toString());
              throw new SANYExitException(-1, "FrontEndException: " + fe.toString());
            }

            if (doDebugging) {
              // Run the Semantic Graph Exploration tool
              Explorer explorer = new Explorer(spec.getExternalModuleTable(), spec.getSemanticErrors());
              try {
                explorer.main(args);
              }
              catch (ExplorerQuitException e) { /*do nothing*/ }
            }
      } else 
      {
          out.log(LogLevel.ERROR, "Cannot find the specified file %s.", args[i]);
          throw new SANYExitException(-1, "Cannot find file: " + args[i]);
      }
    }
  }

}
