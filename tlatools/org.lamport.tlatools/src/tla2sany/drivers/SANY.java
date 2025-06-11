

// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.drivers;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import tla2sany.explorer.Explorer;
import tla2sany.explorer.ExplorerQuitException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Context;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.Generator;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.SemanticNode;
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

  private static boolean doParsing          = true;  
    // true <=> parsing should be done
    //          currently there is no way to turn this off

  private static boolean doSemanticAnalysis = true;  
    // true <=> semantic analysis should be done
    //          default is true; turned OFF by -S switch

  private static boolean doLevelChecking    = true;  
    // true <=> level checking should be done
    //          no effect if doSemanticAnalysis is false
    //          default is true; turned OFF by -L switch

  private static boolean doDebugging        = false; 
    // true <=> control should be transferred to debugger;
    //          default is false; turned ON by -D switch

  private static boolean doStrictErrorCodes   = false;
    // true <=> error level should be reported as the tools'
    //          return value

  /**
   * The SANY.frontEndMain method Processes an entire TLA+ spec
   * that starts in the file named in "filename", including all files
   * it refers to directly or indirectly in EXTENDS or INSTANCE
   * constructs.  "fileName" is relative to the current directory.  It
   * is expected to end with the extension ".tla"; if it does not,
   * then ".tla" is appended before processing it.
   *
   * This method does (1) parsing, (2) semantic analysis, and (3)
   * level-checking, and returns a Specification object, which is the
   * root of the semantic graph of the specification.
   *
   * It also sends progress indications and a text error stream
   * suitable for printing on System.out or System.err to the
   * PrintStream "syserr" (unless "syserr" is null).  The error stream
   * is also saved in Errors objects that are components of the
   * Specification object returned.  The caller may prefer to pass
   * syserr = null, and use the these Errors objects to provide
   * feedback to the human spec-writer in some other way.
   *
   * This method returns a Specification object, even if warnings,
   * errors, or aborts occurred during processing.  (But the
   * Specification may be incomplete, in that not all modules or
   * definitions are processed.)

   * The Specification object returned must be queried by the caller
   * using getErrorLevel() to see what level of problems, if any,
   * occurred during the three phases.  Any value from getErrorLevel()
   * other than 0 is fatal, and the caller should not use the
   * specification object any more.
   *
   * This method throws a FrontEndException if an unexpected runtime
   * error occurs in the FrontEnd.  This exception is NOT thrown for
   * ordinary Warning, Error, or Abort conditions detected during
   * processing--those are reported in the returned specification
   * object, which must be checked as described above.
   */
  public static final int frontEndMain(
                             SpecObj spec, 
                             String fileName, 
                             PrintStream syserr) throws FrontEndException {
    try {
      // **** Initialize the global environment
      frontEndInitialize();
    
      // **** Parsing 
      if (doParsing) frontEndParse(spec, syserr);
    
      // **** Semantic analysis and level checking
      if (doSemanticAnalysis) 
            {frontEndSemanticAnalysis(spec, syserr, doLevelChecking);} ;
    }
    catch (ParseException pe) {
      return -1;
    }
    catch (SemanticException se) {
      return -1;
    }
    catch (Exception e) {
      // e.printStackTrace(syserr);
      syserr.println(e.toString());
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
  public static void frontEndInitialize() {
    Context.reInit();
  } // frontEndInitialize

  // Parse all of the files referred to by the top-level file in specification
  public static void frontEndParse(SpecObj spec, PrintStream syserr) 
  throws ParseException {
	  frontEndParse(spec, syserr, true);
  }
  public static void frontEndParse(SpecObj spec, PrintStream syserr, boolean validatePCalTranslation) 
  throws ParseException {
      /***********************************************************************
       * Modified on 12 May 2008 by LL to remove "throws AbortException",     *
       * since it catches all exceptions and turns them into                  *
       * ParseExceptions.                                                     *
       ***********************************************************************/
      try 
      {
          // Actual parsing method called from inside loadSpec()
          if (!spec.loadSpec(spec.getFileName(), spec.parseErrors, validatePCalTranslation, syserr)) 
          {
              // dead code SZ 02. Aug 2009
              /*
        spec.parseErrors.addError(
            Location.nullLoc,
            "Parsing failed; semantic analysis not started");
               */
          }

          if (!spec.parseErrors.isSuccess()) 
          {
              if (syserr!= null) syserr.println( spec.parseErrors );

              // indicate fatal error during parsing phase
              spec.errorLevel = 2;
              throw new ParseException(); 
          }
      }
      // TODO
      catch (ParseException e) 
      {
          // get here if either the TLAPlusParser.parse() threw a ParseException or spec.ParseErrors was not empty
          throw new ParseException();
      }
      catch (Exception e) 
      {
          // Assert.printStack(e);
          syserr.println("\nFatal errors while parsing TLA+ spec in file " + 
                  spec.getFileName() + "\n"); 

          syserr.println(e.toString()); 
          // syserr.println("Parsing errors detected before unexpected exception:\n");
          syserr.print( spec.parseErrors );

          throw new ParseException();
      }
      return;
  } //

  public static void frontEndSemanticAnalysis(SpecObj spec,
                                              PrintStream syserr,
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
          syserr.println("Semantic processing of module " + moduleStringName);
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
            syserr.println("Semantic errors:\n\n" + semanticErrors);
            // indicate fatal error during semantic analysis or level-checking
            if ( semanticErrors.getNumErrors() > 0 ) {
              spec.errorLevel = 4;
            } // end if
          } // end if
        } // end if
      } // end while
    }
    catch (AbortException e) {
      if ( syserr != null) {
        syserr.println("Fatal errors in semantic processing of TLA spec " +
                       spec.getFileName() + "\n" + e.getMessage() +
                       "\nStack trace for exception:\n"); 
        e.printStackTrace(syserr);
      }
  
      if (semanticErrors.getNumMessages() > 0) {
        if ( syserr != null ) {
          syserr.println("Semantic errors detected before the unexpected exception:\n");
          syserr.print("\n" + semanticErrors);
        }
        
        // indicate fatal error during semantic analysis or level-checking
        if ( semanticErrors.getNumErrors() > 0 ) { 
          spec.errorLevel = 4;
        }
      }
      throw new SemanticException(e);
    }
    return;
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
    if (args.length == 0) {
      printUsage();
      System.exit(-1);
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
           System.exit(0);
      } else {
           ToolIO.out.println("Invalid option: " + args[i]);
           ToolIO.out.println("Try 'SANY -help' for more information.");
           System.exit(-1);
      }
    }

    if (i == args.length) {
      ToolIO.out.println("At least 1 filename is required.");
      ToolIO.out.println("Try 'SANY -help' for more information.");
      System.exit(-1);
    }

    // After the termination of the previous loop, the remaining
    // elements on the command line must be file names for specifications.

    // For each file named on the command line (i.e. in the args
    // array) (re)initialize the entire system and process that file
    // as the root of a new specification.
    for ( ; i < args.length; i++) {
      // continue the loop where the last one left off
      // Print documentation line on System.out
      ToolIO.out.println("\n****** SANY2 " + version + "\n") ;

      // Get next file name from command line; then parse,
      // semantically analyze, and level check the spec started in
      // file Filename leaving the result (normally) in Specification
      // spec.
      SpecObj spec = new SpecObj(args[i], null);
      // check if file exists
      if (FileUtil.createNamedInputStream(args[i], spec.getResolver()) != null) 
      {
          try {
              int ret = frontEndMain(spec, args[i], ToolIO.out);
			  if (ret != 0) {
            	  System.exit(ret);
              }
            }
            catch (FrontEndException fe) {
              // For debugging
              fe.printStackTrace();   
              ToolIO.out.println(fe);
              System.exit(-1);
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
          ToolIO.out.println("Cannot find the specified file " + args[i] + ".");
          System.exit(-1);
      }
    }
  }

}
