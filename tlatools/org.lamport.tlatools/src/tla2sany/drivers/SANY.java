

// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.drivers;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import tla2sany.explorer.Explorer;
import tla2sany.explorer.ExplorerQuitException;
import tla2sany.linter.Linter;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ErrorCode;
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
   * Set of message codes to silence by default
   */
  private static final Set<ErrorCode> defaultSuppressedCodes = Set.of();

  /**
   * Set of message codes to elevate to errors by default
   */
  private static final Set<ErrorCode> defaultMessagesAsErrorCodes = Set.of();

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
   * Use {@link SANY#parse(SpecObj, String, SanyOutput, SanySettings)}
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
        doValidatePCalTranslationDefault,
        defaultSuppressedCodes,
        defaultMessagesAsErrorCodes
      );
    return parse(spec, fileName, out, settings).code();
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
   * the root of the semantic graph of the specification. The later parser
   * phases can be optionally disabled using the {@link SanySetting} object.
   *
   * This method sends progress indications and other log messages to the
   * {@link SanyOutput} parameter. Errors and warnings (along with machine-
   * readable metadata) are furthermore saved to an {@link Errors} instance
   * in the spec object for later processing. If no human-readable log output
   * is desired, a {@link tla2sany.output.SilentSanyOutput} instance should
   * be provided.
   *
   * For backwards compatibility reasons, detecting & handling the possible
   * error cases of this method is somewhat complicated. First of all, this
   * method returns a {@link SanyExitCode} instance. If this is any other
   * value than {@link SanyExitCode#OK}, there has been a failure and the
   * spec object cannot be used. Secondly, this method can throw a
   * {@link FrontEndException} if the error is particularly bad, which must
   * be caught & handled by the caller; in this case the spec object also
   * cannot be used. You might expect that when this method returns
   * {@link SanyExitCode#OK} you are in the clear, but unfortunately this is
   * not so. In this case you should call {@link SpecObj#getErrorLevel()} to
   * see whether it is nonzero. If it is nonzero, spec again cannot be used.
   * However, if it is zero, then you should also check {@link SpecObj#getParseErrors()}
   * and {@link SpecObj#getSemanticErrors()} by calling the {@link Errors#isSuccess()}
   * method on each. If these are both true, then at that point you can be
   * assured that the spec object is ready for use.
   *
   * This method throws a {@link FrontEndException} if an unexpected runtime
   * error occurs during parsing. This exception is NOT thrown for ordinary
   * {@link tla2sany.semantic.ErrorCode.ErrorLevel.WARNING} or
   * {@link tla2sany.semantic.ErrorCode.ErrorLevel.ERROR} occurrences, which
   * are reported through the {@link Errors} instances as explained above.
   */
  public static final SanyExitCode parse(
                             SpecObj spec, 
                             String fileName, 
                             SanyOutput out,
                             SanySettings settings) throws FrontEndException {
    try {
      // **** Initialize the global environment
      frontEndInitialize();
    
      // **** Parsing 
      frontEndParse(spec, out, settings);
    
      // **** Semantic analysis and level checking
      if (settings.doSemanticAnalysis) {
        frontEndSemanticAnalysis(spec, out, settings);

        // **** Linting
        if (settings.doLevelChecking && SanyExitCode.OK == SanyExitCode.fromCode(spec.getErrorLevel()) && settings.doLinting) {
          final int warnsBefore = spec.semanticErrors.getWarningDetails().size();
          frontEndLinting(spec, out);
          // Print linting warnings, respecting suppressed/elevated codes.
          final List<ErrorDetails> allWarnings = spec.semanticErrors.getWarningDetails();
          final List<ErrorDetails> lintingWarnings = allWarnings.subList(warnsBefore, allWarnings.size());
          final boolean errorElevated = reportMessages(out, filterVisibleMessages(lintingWarnings, settings), settings);
          if (errorElevated) {
            spec.errorLevel = SanyExitCode.SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE.code();
          }
        }
      }
    }
    catch (ParseException pe) {
      return SanyExitCode.ERROR;
    }
    catch (SemanticException se) {
      return SanyExitCode.ERROR;
    }
    catch (Exception e) {
      out.log(LogLevel.ERROR, e.toString());
      throw new FrontEndException(e);
    }

    return settings.doStrictErrorCodes
        ? SanyExitCode.fromCode(spec.getErrorLevel())
        : SanyExitCode.OK;
  }

  /**
   * Checks if a message should be treated as an error.
   */
  private static boolean isMessageElevated(ErrorDetails message, SanySettings settings) {
    return settings.messagesAsErrorCodes.contains(message.getCode());
  }

  /**
   * Filters the visible messages based on the settings.
   */
  private static List<ErrorDetails> filterVisibleMessages(List<ErrorDetails> messages, SanySettings settings) {
    return messages.stream()
        .filter(w -> !settings.suppressedCodes.contains(w.getCode()))
        .collect(Collectors.toList());
  }

  /**
   * Reports the messages to the output. Returns true if any elevated messages were encountered.
   */
  private static boolean reportMessages(SanyOutput out, List<ErrorDetails> messages, SanySettings settings) {
    boolean errorElevated = false;
    // Print non-elevated messages first.
    for (ErrorDetails message : messages) {
      if (!isMessageElevated(message, settings)) {
        out.log(LogLevel.WARNING, "%s\n\n\n", message);
      }
    }
    // Print elevated messages as errors.
    for (ErrorDetails message : messages) {
      if (isMessageElevated(message, settings)) {
        out.log(LogLevel.ERROR, "Warning treated as error: %s\n\n\n", message);
        errorElevated = true;
      }
    }
    return errorElevated;
  }

  /** 
   * Initialize the all parts of the FrontEnd to handle a new specification.
   */
  public static void frontEndInitialize() {
    Context.reInit();
  } // frontEndInitialize

  /**
   * Use {@link SANY#frontEndParse(SpecObj, SanyOutput, SanySettings)} instead for greater
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
   * Use {@link SANY#frontEndParse(SpecObj, SanyOutput, SanySettings)} instead for greater
   * control of output.
   */
  @Deprecated
  public static void frontEndParse(SpecObj spec, PrintStream sysErr, boolean validatePCalTranslation)
    throws ParseException {
    frontEndParse(spec, new SimpleSanyOutput(sysErr, LogLevel.INFO), validatePCalTranslation);
  }

  /**
   * Use {@link SANY#frontEndParse(SpecObj, SanyOutput, SanySettings)} instead.
   */
  @Deprecated
  public static void frontEndParse(SpecObj spec, SanyOutput out, boolean validatePCalTranslation)
  throws ParseException {
    SanySettings settings = new SanySettings(
      doStrictErrorCodes,
      doSemanticAnalysis,
      doLevelChecking,
      doLinting,
      validatePCalTranslation,
      defaultSuppressedCodes,
      defaultMessagesAsErrorCodes
    );

    frontEndParse(spec, out, settings);
  }

  /**
   * Parses the specification.
   */
  public static void frontEndParse(SpecObj spec, SanyOutput out, SanySettings settings)
  throws ParseException {
      /***********************************************************************
       * Modified on 12 May 2008 by LL to remove "throws AbortException",     *
       * since it catches all exceptions and turns them into                  *
       * ParseExceptions.                                                     *
       ***********************************************************************/
      try 
      {
          // Actual parsing method called from inside loadSpec()
          spec.loadSpec(spec.getFileName(), spec.parseErrors, settings.validatePCalTranslation, out);

          List<ErrorDetails> warnings = spec.parseErrors.getWarningDetails();
          // Filter and display warnings, respecting suppressed/elevated codes.
          final List<ErrorDetails> visibleWarnings = filterVisibleMessages(warnings, settings);
          if (!visibleWarnings.isEmpty()) {
            out.log(LogLevel.WARNING, "Warnings (%d) during syntax parsing of %s:\n\n", visibleWarnings.size(), spec.getFileName());
            final boolean errorElevated = reportMessages(out, visibleWarnings, settings);
            if (errorElevated) {
              spec.errorLevel = SanyExitCode.SYNTAX_PARSING_FAILURE.code();
            }
          }

          if (!spec.parseErrors.isSuccess()) 
          {
              out.log(LogLevel.ERROR, spec.parseErrors.toString());
              // indicate fatal error during parsing phase
              spec.errorLevel = SanyExitCode.SYNTAX_PARSING_FAILURE.code();
              throw new ParseException(); 
          }
      }
      catch (ParseException e) 
      {
          // get here if either the TLAPlusParser.parse() threw a ParseException or spec.ParseErrors was not empty
          spec.errorLevel = SanyExitCode.SYNTAX_PARSING_FAILURE.code();
          throw new ParseException();
      }
      catch (Exception e) 
      {
          spec.errorLevel = SanyExitCode.SYNTAX_PARSING_FAILURE.code();
          out.log(LogLevel.ERROR, "\nFatal errors while parsing TLA+ spec in file %s\n", spec.getFileName());
          out.log(LogLevel.ERROR, e.toString());
          out.log(LogLevel.ERROR, spec.parseErrors.toString());
          throw new ParseException();
      }
      return;
  } //

  /**
   * Use {@link SANY#frontEndSemanticAnalysis(SpecObj, SanyOutput, SanySettings)}
   * for greater control over output.
   */
  @Deprecated
  public static void frontEndSemanticAnalysis(SpecObj spec,
                                              PrintStream syserr,
                                              boolean levelCheck) 
  throws SemanticException {
    frontEndSemanticAnalysis(spec, new SimpleSanyOutput(syserr, LogLevel.INFO), levelCheck);
  }

  /**
   * Use {@link SANY#frontEndSemanticAnalysis(SpecObj, SanyOutput, SanySettings)} instead.
   */
  @Deprecated
  public static void frontEndSemanticAnalysis(SpecObj spec,
                                              SanyOutput out,
                                              boolean levelCheck) 
  throws SemanticException {
    SanySettings settings = new SanySettings(
      doStrictErrorCodes,
      doSemanticAnalysis,
      levelCheck,
      doLinting,
      doValidatePCalTranslationDefault,
      defaultSuppressedCodes,
      defaultMessagesAsErrorCodes
    );
    frontEndSemanticAnalysis(spec, out, settings);
  }

  /**
   * Performs semantic analysis on the specification.
   */
  public static void frontEndSemanticAnalysis(SpecObj spec,
                                              SanyOutput out,
                                              SanySettings settings)
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
          if (moduleNode != null && semanticErrors.isSuccess() && settings.doLevelChecking ) {
            moduleNode.levelCheck(semanticErrors);
          }

          // Indicate in the externalModuleTable that the last module
          // analyzed is the root ModuleNode
          if (i == spec.semanticAnalysisVector.size()-1) { 
            externalModuleTable.setRootModule( moduleNode ); 
          }

          if (semanticErrors.getNumMessages() > 0) {
            // Print warnings, respecting suppressed/elevated codes
            final List<ErrorDetails> allWarnings = semanticErrors.getWarningDetails();
            final List<ErrorDetails> visibleWarnings = filterVisibleMessages(allWarnings, settings);
            if (!visibleWarnings.isEmpty()) {
              out.log(LogLevel.WARNING, "*** Warnings: %d\n", visibleWarnings.size());
              final boolean errorElevated = reportMessages(out, visibleWarnings, settings);
              if (errorElevated) {
                spec.errorLevel = SanyExitCode.SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE.code();
              }
            }

            // Print errors at ERROR level.
            final List<ErrorDetails> errors = semanticErrors.getErrorDetails();
            if (!errors.isEmpty()) {
              out.log(LogLevel.ERROR, "Semantic errors:\n\n*** Errors: %d\n", errors.size());
              for (ErrorDetails error : errors) {
                out.log(LogLevel.ERROR, "%s\n\n", error);
              }
            }

            // indicate fatal error during semantic analysis or level-checking
            if ( semanticErrors.getNumErrors() > 0 ) {
              spec.errorLevel = SanyExitCode.SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE.code();
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
          spec.errorLevel = SanyExitCode.SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE.code();
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
          "-suppressMessages", "codes",
          "Suppress specific messages; comma-separated list of message codes.\n" +
          "Suppressed messages are not printed and do not cause SANY to fail.\n" + 
          "Errors cannot be suppressed.\n " +
          "Message codes can be found in https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tla2sany/semantic/ErrorCode.java#L38", true));
      variant.add(new UsageGenerator.Argument(
          "-messagesAsErrors", "codes",
          "Treat specific message codes as errors; comma-separated list of message codes.\n" +
          "When triggered, SANY exits with failure.\n" +
          "Message codes can be found in https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tla2sany/semantic/ErrorCode.java#L38", true));
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
      throw new SANYExitException(SanyExitCode.ERROR, "No arguments provided");
    }
    // set of message codes to silence; populated by -suppressMessages CLI flag
    final Set<ErrorCode> suppressedCodes = new HashSet<>();

    // set of message codes to elevate to errors; populated by -messagesAsErrors CLI flag
    final Set<ErrorCode> messagesAsErrorCodes = new HashSet<>();

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
      else if (args[i].toLowerCase().equals("-suppressmessages")) {
           i++;
           if (i >= args.length) {
             ToolIO.out.println("Error: -suppressMessages requires a comma-separated list of codes.");
             throw new SANYExitException(SanyExitCode.ERROR, "-suppressMessages requires an argument");
           }
           for (String token : args[i].split(",")) {
             token = token.trim();
             try {
               final int code = Integer.parseInt(token);
               final ErrorCode messageCode = ErrorCode.fromStandardValue(code); // validate; throws if unknown
               if (messageCode.getSeverityLevel() == ErrorCode.ErrorLevel.ERROR) {
                 ToolIO.out.println("Error: -suppressMessages: code " + token + " is an error and cannot be suppressed.");
                 throw new SANYExitException(SanyExitCode.ERROR, "-suppressMessages: unsuppressable code: " + token);
               }
               suppressedCodes.add(messageCode);
             } catch (NumberFormatException nfe) {
               ToolIO.out.println("Error: -suppressMessages: not an integer: " + token);
               throw new SANYExitException(SanyExitCode.ERROR, "-suppressMessages: not an integer: " + token);
             } catch (IllegalArgumentException iae) {
               ToolIO.out.println("Error: -suppressMessages: unknown message code: " + token);
               throw new SANYExitException(SanyExitCode.ERROR, "-suppressMessages: unknown code: " + token);
             }
           }
      }
      else if (args[i].toLowerCase().equals("-messagesaserrors")) {
           i++;
           if (i >= args.length) {
             ToolIO.out.println("Error: -messagesAsErrors requires a comma-separated list of codes.");
             throw new SANYExitException(SanyExitCode.ERROR, "-messagesAsErrors requires an argument");
           }
           for (String token : args[i].split(",")) {
             token = token.trim();
             try {
               final int code = Integer.parseInt(token);
               final ErrorCode errorCode = ErrorCode.fromStandardValue(code); // validate; throws if unknown
               messagesAsErrorCodes.add(errorCode);
             } catch (NumberFormatException nfe) {
               ToolIO.out.println("Error: -messagesAsErrors: not an integer: " + token);
               throw new SANYExitException(SanyExitCode.ERROR, "-messagesAsErrors: not an integer: " + token);
             } catch (IllegalArgumentException iae) {
               ToolIO.out.println("Error: -messagesAsErrors: unknown message code: " + token);
               throw new SANYExitException(SanyExitCode.ERROR, "-messagesAsErrors: unknown code: " + token);
             }
           }
      }
      else if (args[i].toLowerCase().equals("-help")) {
           printUsage();
           return;
      } else {
           ToolIO.out.println("Invalid option: " + args[i]);
           ToolIO.out.println("Try 'SANY -help' for more information.");
           throw new SANYExitException(SanyExitCode.ERROR, "Invalid option: " + args[i]);
      }
    }

    if (i == args.length) {
      ToolIO.out.println("At least 1 filename is required.");
      ToolIO.out.println("Try 'SANY -help' for more information.");
      throw new SANYExitException(SanyExitCode.ERROR, "No filename provided");
    }

    // Check that suppressMessages and messagesAsErrors do not intersect and report an error if they do.
    Set<ErrorCode> intersection = new HashSet<>(suppressedCodes);
    intersection.retainAll(messagesAsErrorCodes);
    if (!intersection.isEmpty()) {
        ToolIO.out.println("Error: The following codes were set to both -suppressMessages and -messagesAsErrors: " + intersection);
        throw new SANYExitException(
            SanyExitCode.ERROR,
            "Options -suppressMessages and -messagesAsErrors overlap for codes: " + intersection
        );
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
              final SanySettings settings = new SanySettings(
                  SANY.doStrictErrorCodes,
                  SANY.doSemanticAnalysis,
                  SANY.doLevelChecking,
                  SANY.doLinting,
                  SANY.doValidatePCalTranslationDefault,
                  suppressedCodes,
                  messagesAsErrorCodes
              );
              final SanyExitCode result = parse(spec, args[i], out, settings);
              if (result != SanyExitCode.OK) {
            	  throw new SANYExitException(result, "Frontend returned error code: " + result.code());
              }
            }
            catch (FrontEndException fe) {
              // For debugging
              fe.printStackTrace();   
              out.log(LogLevel.ERROR, fe.toString());
              throw new SANYExitException(SanyExitCode.ERROR, "FrontEndException: " + fe.toString());
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
          throw new SANYExitException(SanyExitCode.ERROR, "Cannot find file: " + args[i]);
      }
    }
  }

}
