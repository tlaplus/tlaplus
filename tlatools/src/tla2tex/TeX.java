// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS TeX                                                                *
*                                                                          *
* THINGS TO DO:                                                            *
*  - Change Parameters.latexwidth to be a float.  This requires            *
*    rewriting a bunch of code.  (Should do Parameters.latexheight as      *
*    well.)                                                                *
*                                                                          *
*  - Fix the following bug: the program always reports "More tla           *
*    environments than the last time file run through LaTeX" if            *
*    there is a tla environment after the \end{document}, though           *
*    it hardly seems worth it.                                             *
*                                                                          *
*  - Bug: TLATeX has an unrecoverable error "I/O error: null" if           *
*    it encounters a tla environment containing only a single blank        *
*    line.
*                                                                          *
* Modified on 19 Sep 2007 for TLA+2.  See the comments in TLA.java to see  *
* how.  However, the formatting of proof steps in a tla environment isn't  *
* working right.  If the formula for a step is continued on one or more    *
* subsequent lines, those lines are indented too much.                     *
*                                                                          *
* The `main' method is the TLATeX.TeX program.  It calls other methods to  *
* do the work as follows.                                                  *
*                                                                          *
* BuiltInSymbols.Initialize                                                *
*    Initializes tables containing information about TLA's built-in        *
*    symbols.                                                              *
*                                                                          *
* FormatComments.Initialize                                                *
*    Initializes tables used for formatting comments.  One table           *
*    contains common English words, which are read from the file           *
*    Parameters.WordFile                                                   *
*                                                                          *
* ReadLogFile                                                              *
*    Reads the log file created the last time LaTeX was run on the         *
*    input file.  It returns an array of floats, representing the          *
*    values in points of the \linewidth in effect at each tla              *
*    environment.                                                          *
*                                                                          *
* It next copies the input file to the new version, through the            *
* \begin{document}, and saves it as a vector of lines in the variable      *
* preamble.  It then copies the rest of the file to the new version.       *
* However, after it copies a tla environment, the program skips an         *
* immediately following tlatex environment if one exists.  It then writes  *
* out a new tlatex environment by calling the following sequence of        *
* methods.  It continues doing this until it finds an \end{document}.      *
*                                                                          *
*  TokenizeSpec.Tokenize                                                   *
*    Reads the input file and turns it into an array of array of Token     *
*    objects `spec', where spec[i][j] is item j on line i.  Each line of   *
*    a comment is a single token.  (In the Java program, all numbering     *
*    starts from 0.  The error messages translate into the numbering       *
*    system used by most humans, in which the first object is object       *
*    number 1.)                                                            *
*                                                                          *
*  CommentToken.ProcessComments                                            *
*    Determines which comment tokens are part of a single multi-line       *
*    comment, and indicates this by setting the subtype field of           *
*    comment tokens.                                                       *
*                                                                          *
*  FindAlignments.FindAlignment                                            *
*    Determines what tokens should be aligned with what other tokens.      *
*    This is indicated by setting the tokens' belowAlign and aboveAlign    *
*    fields.  It also sets the isAlignmentPoint flag for each token        *
*    whose left-hand edge is a point used by some other token for its      *
*    alignment.                                                            *
*                                                                          *
*  LaTeXOutput.WriteAlignmentFile                                          *
*    Writes the -alignOut file.                                            *
*                                                                          *
*  LaTeXOutput.RunLaTeX                                                    *
*    Runs LaTeX on the -alignOut file.  This aux file produced by LaTeX    *
*    contains the information about the typeset widths of text that        *
*    TLATeX needs to perform the alignment.                                *
*                                                                          *
*  LaTeXOutput.SetDimensions                                               *
*    Reads the LaTeX aux file and determines how much space it needs to    *
*    add for alignment, setting the information in the tokens'             *
*    distFromMargin and preSpace fields.                                   *
*                                                                          *
*  LaTeXOutput.WriteTLATeXEnvironment                                      *
*    Actually writes the tlatex environment.                               *
*                                                                          *
* When it encounters an \end{document}, the program stops looking for tla  *
* environments and just copies the rest of the input to the new file.      *
* Finally, it renames the files to give the input the extension .old, and  *
* the new version the extension .tex.                                      *
***************************************************************************/
package tla2tex ;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.Vector;

import util.ToolIO;

class TeX
 {                                            // BEGIN class

  static final String lastModified = 
    /***********************************************************************
    * The following string is inserted by an Emacs macro when a new        *
    * version is saved.                                                    *
    ***********************************************************************/
    "last modified on Wed 12 Apr 2013 at 16:08:49 PST by lamport";

  static String modDate = lastModified.substring(21, 33) ;
    /***********************************************************************
    * The modification date.                                               *
    ***********************************************************************/

  static String version = 
    "tla2tex.TeX Version 1.0 created " + modDate ;

    public static void main(String[] args) 
    { /*********************************************************************
      * Get the command-line arguments.                                    *
      *********************************************************************/
      long startTime = Debug.now();
      ToolIO.out.println(version) ;
      GetArguments(args);

      /*********************************************************************
      * Initialize class BuiltInSymbols.                                   *
      *********************************************************************/
      Starting("BuiltInSymbols.Initialize") ;
      BuiltInSymbols.Initialize();
      Finished("BuiltInSymbols.Initialize") ;

      /*********************************************************************
      * Initialize class FormatComments.                                   *
      *********************************************************************/
      Starting("FormatComments.Initialize");
      FormatComments.Initialize();
      Finished("FormatComments.Initialize");

      /*********************************************************************
      * Obtain the linewidths from the log file.                           *
      *********************************************************************/
      float[] lineWidths = ReadLogFile();

      /*********************************************************************
      * Open the input and output files.                                   *
      *********************************************************************/
      BufferedReader infile = null ;
      try 
       { infile = new BufferedReader(new FileReader(Parameters.TLAInputFile));
       }
      catch (Exception e)
       { Debug.ReportError(
          "Can't open input file " + Parameters.TLAInputFile);
       }

      OutputFileWriter outfile = null ;
      try      
       { outfile = new OutputFileWriter(Parameters.LaTeXOutputFile + ".new");
       }
      catch (Exception e)
       { Debug.ReportError(
          "Can't open output file " + Parameters.LaTeXOutputFile + ".new");
       }

      int lineNum = 0 ;
        /*******************************************************************
        * The number of lines read from the input file.                    *
        *******************************************************************/
        
      /*********************************************************************
      * Copy the preamble (everything through the line containing          *
      * \begin{document}, and save everything except the                   *
      * \begin{document} in the Vector preamble.                           *
      *********************************************************************/
      Vector preamble = new Vector(200);
      String line = "" ;
      try
       { line = infile.readLine();
         while (   (line != null)
                && (line.indexOf("\\begin{document}") == -1))
          { lineNum = lineNum + 1 ;
            outfile.putLine(line) ;
            preamble.addElement(line);
            line = infile.readLine();
          }
       }
      catch (Exception e)
       { Debug.ReportError("I/O error: " + e.getMessage());
       }
      if (line == null)
       { Debug.ReportError("Input file has no \\begin{document}"); }
      lineNum = lineNum + 1 ;

      /*********************************************************************
      * Write out the \begin{document} line                                *
      *********************************************************************/
      outfile.putLine(line) ;


      /*********************************************************************
      * If there's something before the \begin{document} on the line, add  *
      * it to preamble.                                                    *
      *********************************************************************/
      int begindocPos = line.indexOf("\\begin{document}") ;
      if (begindocPos != 0)
       { preamble.addElement(line.substring(0, begindocPos));
       }
        
      /*********************************************************************
      * Process the body of the input file.                                *
      *********************************************************************/
      try
       { line = infile.readLine();
         int envNum = 0 ;
           /****************************************************************
           * The number of tla, pcal, or ppcal environments processed so   *
           * far.                                                          *
           ****************************************************************/

         while (line != null)
          {                                   // BEGIN while (line != null)
           lineNum = lineNum + 1 ;
           outfile.putLine(line) ;
           
           /*
            * If this line begins a tla, pcal, or ppcal environment, set
            * mode to the correct mode for calling TokenizeSpec and set
            * envName to "tla", "pcal", or "ppcal"
            */
           int mode = -1 ;
           String envName = "" ;
           if (line.indexOf("\\begin{tla}") != -1) {
               mode = TokenizeSpec.TLA ;
               envName = "tla" ;
           }
           else if (line.indexOf("\\begin{pcal}") != -1) {
               mode = TokenizeSpec.PLUSCAL ;
               envName = "pcal" ;
           }
           else if (line.indexOf("\\begin{ppcal}") != -1) {
               mode = TokenizeSpec.P_PLUSCAL ;
               envName = "ppcal" ;
           }       
           if (mode != -1)
            {        // BEGIN then OF if (mode != -1)
             /**************************************************************
             * Process the tla/pcal/ppcal environment and set line to the  *
             * line immediately after it or the following tlatex           *
             * environment.                                                *
             *                                                             *
             * Start by copying the environment and also putting it in     *
             * the vector tla.                                             *
             *                                                             *
             * Note: Nothing on the same line may follow a \begin{tla} or  *
             * precede an \end{tla}, and similarly for pcal and ppcal.     *
             **************************************************************/
             Starting(envName + " environment number " + (envNum + 1) 
                         + " on line " + (lineNum + 1));
             Vector tla = new Vector(100);
             int tlaLineNum = lineNum ;
             line = infile.readLine();
             while (   (line != null) 
                    && (line.indexOf("\\end{" + envName + "}") == -1))
              { lineNum = lineNum + 1 ;
                outfile.putLine(line) ;
                tla.addElement(line);
                line = infile.readLine();
              }

             if (line == null)
              { Debug.ReportError( "Unmatched \\begin{" + envName + "} on line " 
                                    + (tlaLineNum + 1)); 
              }
             lineNum = lineNum + 1 ;

             /**************************************************************
             * Write out the \end{tla} line                                *
             **************************************************************/
             outfile.putLine(line) ;

             /**************************************************************
             * Read next line, reporting an error if there is none.        *
             **************************************************************/
             line = infile.readLine();
             if (line == null)
              { Debug.ReportError("Missing \\end{document}"); }

             /**************************************************************
             * If next line begins a tlatex environment, then skip over    *
             * that environment and read the line beyond it.               *
             **************************************************************/
             if (line.indexOf("\\begin{tlatex}") != -1)
              { lineNum = lineNum + 1 ;
                line = infile.readLine();
                while (   (line != null) 
                       && (line.indexOf("\\end{tlatex}") == -1))
                 { lineNum = lineNum + 1 ;
                   line = infile.readLine();
                 }
                if (line == null)
                 { Debug.ReportError( "Unmatched \\begin{tlatex} on line " 
                                    + (tlaLineNum + tla.size() + 2)); 
                 }
                lineNum = lineNum + 1 ;
                line = infile.readLine();
                
              }     

            /***************************************************************
            * Tokenize the spec.                                           *
            ***************************************************************/
            CharReader tlaRdr = new VectorCharReader(tla, tlaLineNum);
            Token[][] spec = TokenizeSpec.Tokenize(tlaRdr, mode);

            /***************************************************************
            * Finish the tokenization by converting sequences of tokens    *
            * that represent proof-step numbers to PF_STEP tokens.         *
            ***************************************************************/
            Token.FindPfStepTokens(spec) ;
            
            /*********************************************************************
            * Really finish the tokenization by parentheses and braces that are  *
            * part of the PlusCal C-syntax to tokens that are printed            *
            * appropriately.                                                     *
            *********************************************************************/
            TokenizeSpec.FixPlusCal(spec, true) ;
             
            /***************************************************************
            * Process the comment tokens.                                  *
            ***************************************************************/
            CommentToken.ProcessComments(spec);

            /***************************************************************
            * Add the alignment pointers to spec.                          *
            ***************************************************************/
            FindAlignments.FindAlignments(spec);      
            // Debug.print2DArray(spec, "spec"); 

            /***************************************************************
            * Find the linewidth for this tla/pcal/ppcal environment.      *
            ***************************************************************/
            float linewidth = -1 ;
            if (envNum < lineWidths.length)
             { linewidth = lineWidths[envNum];
             }
            else
             { if (envNum == lineWidths.length)
                 { ToolIO.out.println(
                      "More tla/pcal/ppcal environments than the last time file\n"
                    + "    run through LaTeX");
                 }
             }

            /***************************************************************
            * Set the LaTeXtextwidth parameter.  This parameter should     *
            * probably be changed to a float, but hopefully doing things   *
            * to the nearest point is good enough.                         *
            ***************************************************************/
            Parameters.LaTeXtextwidth = (int) linewidth;

            /***************************************************************
            * Write the alignment file, run it through LaTeX, and set the  *
            * dimension information in spec based on the log file          *
            * produced by LaTeX.                                           *
            ***************************************************************/
            LaTeXOutput.WriteTeXAlignmentFile(spec, preamble, linewidth);
            Starting("to LaTeX alignment file.");
            LaTeXOutput.RunLaTeX(Parameters.LaTeXAlignmentFile);
            Finished("LaTeXing alignment file");
            LaTeXOutput.SetDimensions(spec) ;
            // Debug.print2DArray(spec, "");

            /***************************************************************
            * Write the tlatex environment.                                *
            ***************************************************************/
            LaTeXOutput.WriteTLATeXEnvironment(spec, outfile) ;
            Finished("tla/pcal/ppcal environment number " + (envNum + 1));
            envNum = envNum + 1;
            }  // END then OF if (mode != -1)
           else
            {/**************************************************************
             * This line did not begin a tla, pcal, or ppcal environment.  *
             **************************************************************/
             line = infile.readLine();
            }
          }                                  // END while (line != null)
        if (envNum < lineWidths.length)
           { ToolIO.out.println(
               "Fewer tla/pcal/ppcal environments than the last time file\n"
                    + "    run through LaTeX");
           };
        /*******************************************************************
        * Close and rename the files.                                      *
        *******************************************************************/
        infile.close() ;
        outfile.close() ;
        File iFile = new File(Parameters.LaTeXOutputFile + ".tex") ;
        File oFile = new File(Parameters.LaTeXOutputFile + ".new") ;

        /*******************************************************************
        * Delete the old version of the .old file, if there is one.        *
        *******************************************************************/
        (new File(Parameters.LaTeXOutputFile + ".old")).delete();

        if (   !iFile.renameTo(new File(Parameters.LaTeXOutputFile + ".old"))
            || !oFile.renameTo(new File(Parameters.LaTeXOutputFile + ".tex")))
         { Debug.ReportError("Error while renaming files"); }
       }
      catch (Exception e)
       { Debug.ReportError("I/O error: " + e.getMessage());
       }
      
      Debug.printElapsedTime(startTime, "Total execution time:");
    }  // END main


  private static void GetArguments(String[] args)
     /**********************************************************************
     * Get the command-line arguments and set the appropriate parameters.  *
     **********************************************************************/
     { /********************************************************************
       * The following flags are set if the indicated option is present.   *
       ********************************************************************/
       boolean outOption = false;
       boolean alignOutOption = false;
       boolean psOption = false ;
       boolean nopsOption = false ;
       int nextArg = 0 ;
         /******************************************************************
         * The number of the argument being processed.                     *
         ******************************************************************/
       int maxArg = args.length - 1;
         /******************************************************************
         * The number of the final argument, which is the input file name. *
         ******************************************************************/
       if (maxArg < 0)
        { CommandLineError("No arguments specified");
        } ;

       if (   (args[maxArg].length() != 0)
           && (args[maxArg].charAt(0) == '-'))
         /******************************************************************
         * If the last argument begins with "-", then no file has been     *
         * specified.  This should mean that the user has typed "-help"    *
         * or "-info", but it could be another mistake.                    *
         ******************************************************************/
         { maxArg = maxArg + 1 ;
         } ;

       while (nextArg < maxArg)
        /*******************************************************************
        * Process all the arguments, except for the last (unless it's a    *
        * "-" argument).                                                   *
        *******************************************************************/
        { String option = args[nextArg] ;
          if (option.equals("-help"))
            { OutputMessageFile(Parameters.TeXHelpFile) ;
              System.exit(0);
            }
          else if (option.equals("-info"))
            { OutputMessageFile(Parameters.TeXInfoFile) ;
              System.exit(0);
            }
// We're not going to run the output through TeX or dvips.  The
// user can do that.
//          else if (option.equals("-ps"))
//            { psOption = true ; 
//            }
//          else if (option.equals("-nops"))
//            { nopsOption = true ; 
//            }
//          else if (option.equals("-psCommand"))
//            { nextArg = nextArg + 1;
//              if (nextArg >= args.length) 
//                {CommandLineError("No input file specified") ;} ;
//              Parameters.PSCommand = args[nextArg];
//            }
          else if (option.equals("-latexCommand"))
            { nextArg = nextArg + 1;
              if (nextArg >= args.length) 
                {CommandLineError("No input file specified") ;} ;
              Parameters.LaTeXCommand = args[nextArg];
            }
          else if (option.equals("-out"))
            { /*************************************************************
              * The LaTeX output file.                                     *
              *************************************************************/
              outOption = true ;
              nextArg = nextArg + 1;
              if (nextArg >= args.length) 
                {CommandLineError("No input file specified") ;} ;
              Parameters.LaTeXOutputFile = RemoveExtension(args[nextArg]);
              if (HasPathPrefix(Parameters.LaTeXOutputFile))
               { CommandLineError(
                    "-out file contains a path specifier.\n"
                  + "It must be a file in the current directory.");
               };
            }
          else if (option.equals("-alignOut"))
            { /*************************************************************
              * The alignment file.  The default is "tlatex".              *
              *************************************************************/
              alignOutOption = true ;
              nextArg = nextArg + 1;
              if (nextArg >= args.length) 
                {CommandLineError("No input file specified") ;} ;
              Parameters.LaTeXAlignmentFile = RemoveExtension(args[nextArg]);
              if (HasPathPrefix(Parameters.LaTeXAlignmentFile))
               { CommandLineError(
                    "-alignOut file contains a path specifier.\n"
                  + "It must be a file in the current directory.") ;
               };
            } 
          else if (option.equals("-debug"))
            { Parameters.Debug = true;
            }
// Should probably change the way the -number option is implemented
// so numbering is controlled by a LaTeX command, so the user 
// of tlatex.TeX can get lines numbered.
//
//          else if (option.equals("-number"))
//            { Parameters.PrintLineNumbers = true;
//            }
          else 
            { CommandLineError("Unknown option: " + option);
            } ;
          nextArg = nextArg + 1;
        }                      // END while (nextArg < maxArg)

       if (nextArg > maxArg)
         /******************************************************************
         * The last option took an argument that was the last              *
         * command-line argument.                                          *
         ******************************************************************/
         { CommandLineError("No input file specified") ;
         } ;

       /********************************************************************
       * Set Parameters.TLAInputFile to the last argument, adding ".tex"   *
       * if it has no extension already.                                   *
       ********************************************************************/
       if (args[maxArg].indexOf(".") == -1)
         { Parameters.TLAInputFile = args[maxArg] + ".tex";}
       else       
         { Parameters.TLAInputFile = args[maxArg];};

       /********************************************************************
       * Set default options.                                              *
       ********************************************************************/
       if (! outOption)
         { Parameters.LaTeXOutputFile = 
             RemoveExtension(RemovePathPrefix(Parameters.TLAInputFile));
           if (HasPathPrefix(Parameters.TLAInputFile))
             ToolIO.out.println(
              "Warning: Output file being written to a different directory\n"
            + "         than input file.");
         } ;
       if (! alignOutOption)
         { Parameters.LaTeXAlignmentFile = "tlatex" ;
         } ;

       /********************************************************************
       * Produce Postscript output if either                               *
       *   (i) -ps, or                                                     *
       *  (ii) -shade but not -nops                                        *
       * was specified.                                                    *
       ********************************************************************/
       if (   psOption 
           || (Parameters.CommentShading && ! nopsOption))

        { Parameters.PSOutput = true;
        }
     }   

    private static int GetIntArg(String str, String option)
      /*********************************************************************
      * Returns str interpreted as an integer, or generates an error       *
      * message for the indicated option.                                  *
      *********************************************************************/
      {int val = 0; 
       try { val = Integer.parseInt(str) ; }
       catch (NumberFormatException e)
        { CommandLineError(option + " option must specify an integer value");
        };
       return val ;
      }

    private static String RemoveExtension(String fileName)
      /*********************************************************************
      * The string fileName with any extensions removed.                   *
      *********************************************************************/
      { if (fileName.indexOf(".") == -1)
          { return fileName ;}
        else
          { return fileName.substring(0, fileName.indexOf(".")); }
      }      

   private static String RemovePathPrefix(String str)
    /***********************************************************************
    * Returns str with all any leading path specifiers removed.  For       *
    * example, calling it on "c:frob\bar\name.txt" or "~/frob/bar/name.txt"  *
    * will return "name.txt".                                              *
    ***********************************************************************/
    { String result = str;
      if (result.indexOf(":") != -1)
        { result = result.substring(result.lastIndexOf(":")+1) ; } ;
      if (result.indexOf("/") != -1)
        { result = result.substring(result.lastIndexOf("/")+1) ; } ;
      if (result.indexOf("\\") != -1)
        { result = result.substring(result.lastIndexOf("\\")+1) ; } ;
      return result;
    }    

   private static boolean HasPathPrefix(String str)
    /***********************************************************************
    * True iff str has a leading path specifier--that is, if it contains   *
    * a ":", "/" or "\".                                                   *
    ***********************************************************************/
    { return    (str.indexOf(":") != -1)
             || (str.indexOf("/") != -1)
             || (str.indexOf("\\") != -1) ;
    }    

    private static void CommandLineError(String msg)
      /*********************************************************************
      * Announce a command line error with the string indicating the       *
      * explanation, write the help message, and halt.                     *
      *********************************************************************/
      { ToolIO.out.println("TLATeX command-line error: " + msg + ".");
        ToolIO.out.println("Use -help option for more information.");
        // OutputMessageFile(Parameters.HelpFile) ;
        throw new TLA2TexException("TLATeX command-line error: " + msg + "." + "Use -help option for more information.");
      }

    private static void OutputMessageFile(String fileName)
     /**********************************************************************
     * Write the resource file named fileName to stdout.                   *
     **********************************************************************/
     { ResourceFileReader input = new ResourceFileReader(fileName) ;
       String line = input.getLine();
       while (line != null)
         { ToolIO.out.println(line) ;
           line = input.getLine() ;
         } ;
      input.close();
     } ;

    private static long start = Debug.now() ;

    /***********************************************************************
    * Starting / Finished used to print debugging information.            *
    ***********************************************************************/
    private static void Starting(String name)
     { if (Parameters.Debug)
         { start = Debug.now() ;
           ToolIO.out.println("Starting " + name);
         }
     }
    private static void Finished(String name)
     { if (Parameters.Debug)
         { Debug.printElapsedTime(start, name + " finished in");
         }
     }

/*
   private static void MakePSFile()
    { int errorCode = -77;
      String Command =     Parameters.PSCommand + " " 
                         + Parameters.LaTeXOutputFile + ".dvi" ; 
      try { Runtime rt = Runtime.getRuntime() ;
            Process proc = null ;
            proc = rt.exec(Command);
            errorCode = proc.waitFor();
          }
      catch (Exception e)
       { Debug.ReportError(
              "Trying to run the command `" + Command
            + "' produced the following error\n    " + e.getMessage());
       } ;
      if (errorCode < 0)
        { Debug.ReportError(
            "Running the command `" + Command 
          + "' produced an error");
        }
    }    
*/

   private static float[] ReadLogFile()
    /***********************************************************************
    * Reads the log file to obtain the linewidths for the tla              *
    * environments, and returns them as an array of floats.  Each          *
    * linewidth is written to the log file as a separate line such as      *
    *                   \%{123.456}                                        *
    ***********************************************************************/
    { BufferedReader logfile = null ;
      try 
       { logfile = new BufferedReader(
                    new FileReader(Parameters.LaTeXOutputFile + ".log"));
       }
      catch (Exception e)
       { ToolIO.out.println(
               "No file " + Parameters.LaTeXOutputFile + ".log");
         return new float[0];
       }
      Vector resultVec = new Vector(50);
        /*******************************************************************
        * A vector of the strings representing the linewidths.             *
        *******************************************************************/
        
      try
       {String inputLine = logfile.readLine();
        while (inputLine != null)
         { if (   (inputLine.length() > 2)
               && (inputLine.substring(0,3).equals("\\%{")))
            { int start = 3 ;
              int after = inputLine.indexOf("}",start)-2 ;
              resultVec.addElement(inputLine.substring(start, after));
            }; 
           inputLine = logfile.readLine();
         } 
       }
      catch (Exception e)
       { Debug.ReportError(
           "Error reading file " + Parameters.LaTeXOutputFile + ".log");
       }

      float[] result = new float[resultVec.size()];
      int i = 0;
      while (i < result.length)
       { result[i] = Misc.stringToFloat((String) resultVec.elementAt(i));
        i = i+1;
       }
      return result ;
    }
 } 


