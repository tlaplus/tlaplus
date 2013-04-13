// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS TLA                                                                *
* Bug: A string of the form "...'" gets printed as "..."'.                 *
*       Corrected 3 Jan 2005 by modification to tlatex.sty                 *
*                                                                          *
* Bug: The lexing does not allow \bullet_                                  *
*      Corrected 21 Feb 2004                                               *
*                                                                          *
* Bug: The R and X in                                                      *
*                                                                          *
*      ---------------- MODULE frob -------                                *
*      LET RS                                                              *
*      IN  X                                                               *
*      =====================================                               *
*                                                                          *
*      are not aligned.                                                    *
*      CORRECTED 21 Jul 2012.                                              *
*                                                                          *
* Bug:  A weird extra space added to align the \in with the \succ in       *
*                                                                          *
*      LTSet(N, _\succ_, n) == {m \in N : n \succ m}                       *
*      LeadsToInduction(F(_), N, _\succ_, z) ==                            *
*                                                                          *
*      This results from \succ and \in belonging to the same alignment     *
*      class, which is necessary if we want them to both align with = .    *
*      So, this is probably not worth fixing.                              *
*                                                                          *
* Bug: Does not handle hex characters with digits > 9, as in               *
*      \Habc .  The problem is in the tokenizing algorithm in              *
*      TokenizeSpec.Tokenize.  The processing of the BS state in the       *
*      spec needs to handle the "H" or "h" case specially.                 *
* TO DO:                                                                   *
*                                                                          *
*    Try to kludge something so this                                       *
*                                                                          *
*      CASE a -> A                                                         *
*        [] b -> B []                                                      *
*        [] c -> C                                                         *
*                                                                          *
*    does something reasonable.                                            *
*    THE FIX OF 21 Jul 2012 MADE IT DO SOMETHING REASONABLE.               *          
*                                                                          *
* Modified on 19 Sep 2007 as follows for TLA+2:                            *
*  1. Added the new keywords.                                              *
*  2. Added a new PF_STEP token type and various kludges                   *
*     around it to handle proof-step numbers.                              *
*  3. Modified the handling of "!" so it translates to a \bang             *
*     command that primts a small !.  This looks about the same            *
*     in an EXCEPT but looks somewhat better in frob!bar.                  *
*                                                                          *
* Modified on 8 Aug 2012 to handle PlusCal algorithms and add              *
* -noPcalShade option.                                                     *
*                                                                          *                   
* ------------------------------------------------------------------------ *
*                                                                          *
* The `main' method is the TLATeX program.  It calls other methods to do   *
* the work as follows.                                                     *
*                                                                          *
* BuiltInSymbols.Initialize                                                *
*    Initializes tables containing information about TLA's built-in        *
*    symbols.                                                              *
*                                                                          *
* TokenizeSpec.Tokenize                                                    *
*    Reads the input file and turns it into an array of array of Token     *
*    objects `spec', where spec[i][j] is item j on line i.  Each line of   *
*    a comment is a single token.  (In the Java program, all numbering     *
*    starts from 0.  The error messages translate into the numbering       *
*    system used by most humans, in which the first object is object       *
*    number 1.)  This method does not detect PF_STEP tokens such           *
*    as "<2>3a.".                                                          *
*                                                                          *
* TokenizeSpec.FindPfStepTokens                                            *
*    Converts a sequence of tokens that represent a proof step             *
*    number into a single PF_STEP token.                                   *
*                                                                          *
* CommentToken.ProcessComments                                             *
*    Determines which comment tokens are part of a single multi-line       *
*    comment, and indicates this by setting the subtype field of           *
*    comment tokens.                                                       *
*                                                                          *
* FormatComments.Initialize                                                *
*    Initializes tables used for formatting comments.  One table           *
*    contains common English words, which are read from the file           *
*    Parameters.WordFile                                                   *
*                                                                          *
* FindAlignments.FindAlignment                                             *
*    Determines what tokens should be aligned with what other tokens.      *
*    This is indicated by setting the tokens' belowAlign and aboveAlign    *
*    fields.  It also sets the isAlignmentPoint flag for each token        *
*    whose left-hand edge is a point used by some other token for its      *
*    alignment.                                                            *
*                                                                          *
* WriteTLAFile.Write                                                       *
*    Writes the -tlaOut file (if one is specified).                        *
*                                                                          *
* LaTeXOutput.WriteAlignmentFile                                           *
*    Writes the -alignOut file.                                            *
*                                                                          *
* LaTeXOutput.RunLaTeX                                                     *
*    Runs LaTeX on the -alignOut file.  This aux file produced by LaTeX    *
*    contains the information about the typeset widths of text that        *
*    TLATeX needs to perform the alignment.                                *
*                                                                          *
* LaTeXOutput.SetDimensions                                                *
*    Reads the LaTeX aux file and determines how much space it needs to    *
*    add for alignment, setting the information in the tokens'             *
*    distFromMargin and preSpace fields.                                   *
*                                                                          *
* LaTeXOutput.WriteLaTeXFile                                               *
*    Writes the -out file, containing LaTeX input to produce the           *
*    typeset version.                                                      *
*                                                                          *
* LaTeXOutput.RunLaTeX                                                     *
*    Runs LaTeX on the -out file.                                          *
*                                                                          *
* MakePSFile                                                               *
*    If the appropriate options are chosen, it runs the -psCommand         *
*    command on the dvi file produced by LaTeX to produce a Postscript     *
*    or pdf file.                                                          *
***************************************************************************/
package tla2tex;

import java.io.File;
import java.io.IOException;

import util.FileUtil;
import util.ToolIO;

public class TLA
{
    static final String lastModified =
    /***********************************************************************
    * The following string is inserted by an Emacs macro when a new        *
    * version is saved.                                                    *
    ***********************************************************************/
    "last modified on Wed  12 Apr 2013 at 16:06:38 PST by lamport";

    static String modDate = lastModified.substring(21, 33);
    /***********************************************************************
    * The modification date.                                               *
    ***********************************************************************/

    static String version = "tla2tex.TLA Version 1.0 created " + modDate;

    public static void main(String[] args)
    {
        runTranslation(args);
    }

    /**
     * @param args
     */
    public static void runTranslation(String[] args)
    {  
        /*********************************************************************
        * Get the command-line arguments.                                    *
        *********************************************************************/
        long startTime = Debug.now();
        ToolIO.out.println(version);
        GetArguments(args);

        /*********************************************************************
        * Initialize class BuiltInSymbols.                                   *
        *********************************************************************/
        Starting("BuiltInSymbols.Initialize");
        BuiltInSymbols.Initialize();
        Finished("BuiltInSymbols.Initialize");

        /*********************************************************************
        * Read and tokenize the spec.                                        *
        *********************************************************************/
        FileCharReader testlr = new FileCharReader(Parameters.TLAInputFile);
        Starting("TokenizeSpec.Tokenize");
        Token[][] spec = TokenizeSpec.Tokenize(testlr, TokenizeSpec.MODULE);

//System.out.println(TokenizeSpec.skipToUnmatchedEnd(new Position(5, 1), 
//                 spec, false).toString()) ;
//System.out.println(TokenizeSpec.skipToUnmatchedEnd(new Position(5, 1), 
//        spec, true).toString()) ;
//        System.out.println("pcalStart = " + TokenizeSpec.pcalStart.toString());
//        System.out.println("pcalEnd = " + TokenizeSpec.pcalEnd.toString());
        /*********************************************************************
        * Finish the tokenization by converting sequences of tokens that     *
        * represent proof-step numbers to PF_STEP tokens.                    *
        *********************************************************************/
        Token.FindPfStepTokens(spec);
        Finished("TokenizeSpec.Tokenize");
        // Debug.print2DArray(spec, "tok");
        
        /*********************************************************************
        * Really finish the tokenization by parentheses and braces that are  *
        * part of the PlusCal C-syntax to tokens that are printed            *
        * appropriately.                                                     *
        *********************************************************************/
        Starting("TokenizeSpec.FixPlusCal");
        TokenizeSpec.FixPlusCal(spec, false) ;
        Finished("TokenizeSpec.FixPlusCal");

        /*********************************************************************
        * Process the comment tokens.                                        *
        *********************************************************************/
        Starting("CommentToken.ProcessComments");
        CommentToken.ProcessComments(spec);
        Finished("CommentToken.ProcessComments");
        // Debug.print2DArray(spec, "com");

        /*********************************************************************
        * Initialize class FormatComments.                                   *
        *********************************************************************/
        Starting("FormatComments.Initialize");
        FormatComments.Initialize();
        Finished("FormatComments.Initialize");

        /*********************************************************************
        * Add the alignment pointers to spec.                                *
        *********************************************************************/
        Starting("FindAlignments.FindAlignments");
        FindAlignments.FindAlignments(spec);
        Finished("FindAlignments.FindAlignments");
        // Debug.print2DArray(spec, "align");

        /*********************************************************************
        * Write out the tla file with deleted comments removed, if the       *
        * -tlaOut option is chosen.                                          *
        *********************************************************************/
        if (Parameters.TLAOut)
        {
            WriteTLAFile.Write(spec, Parameters.TLAOutFile);
            ToolIO.out.println("Wrote -tlaOut file " + Parameters.TLAOutFile);
        }
        ;

        /*********************************************************************
        * Write the alignment file, run it through LaTeX, and set the        *
        * dimension information in spec based on the log file produced by    *
        * LaTeX.                                                             *
        *********************************************************************/
        Starting("LaTeXOutput.WriteAlignmentFile");
        LaTeXOutput.WriteAlignmentFile(spec);
        Finished("LaTeXOutput.WriteAlignmentFile");

        Starting("LaTeXOutput.RunLaTeX");
        LaTeXOutput.RunLaTeX(Parameters.LaTeXAlignmentFile);
        Finished("LaTeXOutput.RunLaTeX");

        Starting("LaTeXOutput.SetDimensions");
        LaTeXOutput.SetDimensions(spec);
        Finished("LaTeXOutput.SetDimensions");
        // Debug.print2DArray(spec, "");

        /*********************************************************************
        * Write the final LaTeX output and run it through LaTeX.             *
        *********************************************************************/
        Starting("LaTeXOutput.WriteLaTeXFile");
        LaTeXOutput.WriteLaTeXFile(spec);
        Finished("LaTeXOutput.WriteLaTeXFile");

        Starting("LaTeXOutput.RunLaTeX");
        LaTeXOutput.RunLaTeX(Parameters.LaTeXOutputFile);
        Finished("LaTeXOutput.RunLaTeX");

        ToolIO.out.println("TLATeX " + Parameters.LatexOutputExt + " output written on " + 
                Parameters.LaTeXOutputFile + "." +
                Parameters.LatexOutputExt +             
                ((Parameters.MetaDir.equals("")) ? "" : ", from " + Parameters.MetaDir) + ".");
        
        if (Parameters.PSOutput)
        {
            /******************************************************************
            * Produce the Postscript file.                                    *
            ******************************************************************/
            Starting("MakePSFile");
            MakePSFile();
            Finished("MakePSFile");
            ToolIO.out.println("TLATeX Postscript (or pdf) output written on " + Parameters.LaTeXOutputFile
                    + ".ps (or " + Parameters.LaTeXOutputFile + ".pdf).");
        }
        if (! Parameters.MetaDir.equals("")) 
        {
            try
            {
                FileUtil.copyFile(LaTeXOutput.prependMetaDirToFileName(Parameters.LaTeXOutputFile + "."
                        + Parameters.LatexOutputExt), Parameters.TLAInputFile.substring(0, Parameters.TLAInputFile
                        .length()
                        - "tla".length())
                        + Parameters.LatexOutputExt);
            } catch (IOException e)
            {
                Debug.ReportError("Trying to copy output from metadir produced the error:\n" + e.getMessage());
            }

        }
        Debug.printElapsedTime(startTime, "Total execution time:");
    } // END main

    private static void GetArguments(String[] args)
    /**********************************************************************
    * Get the command-line arguments and set the appropriate parameters.  *
    **********************************************************************/
    {
        /********************************************************************
        * The following flags are set if the indicated option is present.   *
        ********************************************************************/
        boolean outOption = false;
        boolean alignOutOption = false;
        boolean psOption = false;
        boolean nopsOption = false;
        
        /********************************************************************
         * These static variables are set to true later in the method if    *
         * the user passes the appropriate argument.                        *
         ********************************************************************/
        Parameters.CommentShading = false;
        Parameters.PrintLineNumbers = false;
        
        int nextArg = 0;
        /******************************************************************
        * The number of the argument being processed.                     *
        ******************************************************************/
        int maxArg = args.length - 1;
        /******************************************************************
        * The number of the final argument, which is the input file name. *
        ******************************************************************/
        if (maxArg < 0)
        {
            CommandLineError("No arguments specified");
        }
        ;

        if ((args[maxArg].length() != 0) && (args[maxArg].charAt(0) == '-'))
        /******************************************************************
        * If the last argument begins with "-", then no file has been     *
        * specified.  This should mean that the user has typed "-help"    *
        * or "-info", but it could be another mistake.                    *
        ******************************************************************/
        {
            maxArg = maxArg + 1;
        }
        ;

        while (nextArg < maxArg)
        /*******************************************************************
        * Process all the arguments, except for the last (unless it's a    *
        * "-" argument).                                                   *
        *******************************************************************/
        {
            String option = args[nextArg];
            if (option.equals("-help"))
            {
                OutputMessageFile(Parameters.HelpFile);
                System.exit(0);
            } else if (option.equals("-info"))
            {
                OutputMessageFile(Parameters.InfoFile);
                System.exit(0);
            } else if (option.equals("-grayLevel"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                try
                {
                    Parameters.PSGrayLevel = Misc.stringToFloat(args[nextArg]);
                } catch (Exception e)
                {
                    CommandLineError("Bad -grayLevel value " + args[nextArg]);
                }
                ;
                // bug found by Yuan Yu in following if statement
                // corrected 9 May 2001
                if ((Parameters.PSGrayLevel > 1) || (Parameters.PSGrayLevel < 0))
                {
                    CommandLineError("-grayLevel value should be between 0 and 1, not "
                            + Misc.floatToString(Parameters.PSGrayLevel, 3));
                }
            } else if (option.equals("-ps"))
            {
                psOption = true;
            } else if (option.equals("-nops"))
            {
                nopsOption = true;
            } else if (option.equals("-psCommand"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.PSCommand = args[nextArg];
            } else if (option.equals("-latexCommand"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.LaTeXCommand = args[nextArg];
            } else if (option.equals("-out"))
            {
                /*************************************************************
                * The LaTeX output file.                                     *
                *************************************************************/
                outOption = true;
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.LaTeXOutputFile = RemoveExtension(args[nextArg]);
                if (HasPathPrefix(Parameters.LaTeXOutputFile))
                {
                    CommandLineError("-out file contains a path specifier.\n"
                            + "It must be a file in the current directory.");
                }
                ;
            } else if (option.equals("-tlaOut"))
            {
                /*************************************************************
                * The tla output file, with TEX comments removed.  Add a     *
                * ".tla" extension if no extension is specified.             *
                *************************************************************/
                Parameters.TLAOut = true;
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.TLAOutFile = args[nextArg];
                if (Parameters.TLAOutFile.indexOf(".") == -1)
                {
                    Parameters.TLAOutFile = Parameters.TLAOutFile + ".tla";
                }
                if (HasPathPrefix(Parameters.TLAOutFile))
                {
                    CommandLineError("-tlaOut file contains a path specifier.\n"
                            + "It must be a file in the current directory.");
                }
                ;
            } else if (option.equals("-alignOut"))
            {
                /*************************************************************
                * The alignment file.                                        *
                *************************************************************/
                alignOutOption = true;
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.LaTeXAlignmentFile = RemoveExtension(args[nextArg]);
                if (HasPathPrefix(Parameters.LaTeXAlignmentFile))
                {
                    CommandLineError("-alignOut file contains a path specifier.\n"
                            + "It must be a file in the current directory.");
                }
                ;
            } else if (option.equals("-debug"))
            {
                Parameters.Debug = true;
            } else if (option.equals("-tlaComment"))
            /***************************************************************
            * This option tells TLATeX to interpret all ambiguous          *
            * identifiers in comments as TLA symbols.                      *
            ***************************************************************/
            {
                Parameters.TLACommentOption = true;
            }
            // else if (option.equals("-notlaComment"))
            // /***************************************************************
            // * The FormatComments.adjustIsTLA method normally sets an *
            // * ambiguous Identifier to a TLA token if it appears somewhere *
            // * in the current comment as a TLA token. This option causes *
            // * the method to do this only if the Identifier is not an *
            // * English word. This option has no effect if the -tlaComment *
            // * option is chosen. *
            // ***************************************************************/
            // { Parameters.NoTLACommentOption = true;
            // }
            else if (option.equals("-shade"))
            {
                Parameters.CommentShading = true;
            } else if (option.equals("-noPcalShade"))
            {
                Parameters.NoPlusCalShading = true;
            }else if (option.equals("-noProlog"))
            {
                Parameters.PrintProlog = false;
            } else if (option.equals("-noEpilog"))
            {
                Parameters.PrintEpilog = false;
            } else if (option.equals("-number"))
            {
                Parameters.PrintLineNumbers = true;
            } else if (option.equals("-style"))
            {
                /*************************************************************
                * Use the specified file as style file in place of           *
                * Parameters.LaTeXModuleProlog.                              *
                *************************************************************/
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.UserStyleFile = RemoveExtension(args[nextArg]);
                if ((Parameters.UserStyleFile != args[nextArg])
                        && (args[nextArg].indexOf(".sty") != args[nextArg].length() - 4))
                {
                    CommandLineError("-style file must have extension `.sty'");
                }
            } else if (option.equals("-ptSize"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.LaTeXptSize = GetIntArg(args[nextArg], option);
                if ((Parameters.LaTeXptSize < 10) || (Parameters.LaTeXptSize > 12))
                {
                    CommandLineError("-ptSize option must be 10, 11, or 12");
                }
                ;
            } else if (option.equals("-textwidth"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.LaTeXtextwidth = GetIntArg(args[nextArg], option);
                if ((Parameters.LaTeXtextwidth < 100) || (Parameters.LaTeXtextwidth > 1000))
                {
                    CommandLineError("-textwidth value of " + Parameters.LaTeXtextwidth + " points is implausible");
                }
                ;
            } else if (option.equals("-textheight"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.LaTeXtextheight = GetIntArg(args[nextArg], option);
                if ((Parameters.LaTeXtextheight < 75) || (Parameters.LaTeXtextheight > 1500))
                {
                    CommandLineError("-textheight value of " + Parameters.LaTeXtextheight + " points is implausible");
                }
                ;
            } else if (option.equals("-hoffset"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.LaTeXhoffset = GetIntArg(args[nextArg], option);
                if ((Parameters.LaTeXhoffset < -250) || (Parameters.LaTeXhoffset > 250))
                {
                    CommandLineError("-hoffset value of " + Parameters.LaTeXhoffset + " points is implausible");
                }
                ;
            } else if (option.equals("-voffset"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.LaTeXvoffset = GetIntArg(args[nextArg], option);
                if ((Parameters.LaTeXvoffset < -250) || (Parameters.LaTeXvoffset > 250))
                {
                    CommandLineError("-voffset value of " + Parameters.LaTeXvoffset + " points is implausible");
                }
                ;
            } else if (option.equals("-metadir"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                ;
                Parameters.MetaDir = args[nextArg];
                Parameters.ParentDir = new File(Parameters.MetaDir);
                if (! Parameters.ParentDir.exists()) {
                  CommandLineError("Specified metdir " + Parameters.MetaDir + 
                          " does not exist.");
                }
            } else if (option.equals("-latexOutputExt"))
            {
                nextArg = nextArg + 1;
                if (nextArg >= args.length)
                {
                    CommandLineError("No input file specified");
                }
                
                Parameters.LatexOutputExt = args[nextArg];
            } else
            {
                CommandLineError("Unknown option: " + option);
            }
            ;
            nextArg = nextArg + 1;
        } // END while (nextArg < maxArg)

        if (nextArg > maxArg)
        /******************************************************************
        * The last option took an argument that was the last              *
        * command-line argument.                                          *
        ******************************************************************/
        {
            CommandLineError("No input file specified");
        }
        ;

        /********************************************************************
        * Set Parameters.TLAInputFile to the last argument, adding ".tla"   *
        * if it has no extension already.                                   *
        ********************************************************************/
        if (args[maxArg].indexOf(".") == -1)
        {
            Parameters.TLAInputFile = args[maxArg] + ".tla";
        } else
        {
            Parameters.TLAInputFile = args[maxArg];
        }
        ;

        /********************************************************************
        * Report an error if TLAInputFile = TLAOutFile.                     *
        ********************************************************************/
        if (Parameters.TLAOutFile.equals(Parameters.TLAInputFile))
        {
            CommandLineError("\n  -tlaOut file the same as the tla input file.\n"
                    + "  This would overwrite your input file, so I won't do it");
        }
        ;

        /********************************************************************
        * Set default options.                                              *
        ********************************************************************/
        if (!outOption)
        {
            Parameters.LaTeXOutputFile = RemoveExtension(RemovePathPrefix(Parameters.TLAInputFile));
        }
        ;
        if (!alignOutOption)
        {
            Parameters.LaTeXAlignmentFile = Parameters.LaTeXOutputFile;
        }
        ;

        /********************************************************************
        * Produce Postscript output if either                               *
        *   (i) -ps, or                                                     *
        *  (ii) -shade but not -nops                                        *
        * was specified.                                                    *
        ********************************************************************/
        if (psOption || (Parameters.CommentShading && !nopsOption))

        {
            Parameters.PSOutput = true;
        }
    }

    private static int GetIntArg(String str, String option)
    /*********************************************************************
    * Returns str interpreted as an integer, or generates an error       *
    * message for the indicated option.                                  *
    *********************************************************************/
    {
        int val = 0;
        try
        {
            val = Integer.parseInt(str);
        } catch (NumberFormatException e)
        {
            CommandLineError(option + " option must specify an integer value");
        }
        ;
        return val;
    }

    private static String RemoveExtension(String fileName)
    /*********************************************************************
    * The string fileName with any extensions removed.                   *
    *********************************************************************/
    {
        if (fileName.indexOf(".") == -1)
        {
            return fileName;
        } else
        {
            return fileName.substring(0, fileName.indexOf("."));
        }
    }

    private static String RemovePathPrefix(String str)
    /***********************************************************************
    * Returns str with all any leading path specifiers removed.  For       *
    * example, calling it on "c:frob\bar\name.txt" or "~/frob/bar/name.txt"  *
    * will return "name.txt".                                              *
    ***********************************************************************/
    {
        String result = str;
        if (result.indexOf(":") != -1)
        {
            result = result.substring(result.lastIndexOf(":") + 1);
        }
        ;
        if (result.indexOf("/") != -1)
        {
            result = result.substring(result.lastIndexOf("/") + 1);
        }
        ;
        if (result.indexOf("\\") != -1)
        {
            result = result.substring(result.lastIndexOf("\\") + 1);
        }
        ;
        return result;
    }

    private static boolean HasPathPrefix(String str)
    /***********************************************************************
    * True iff str has a leading path specifier--that is, if it contains   *
    * a ":", "/" or "\".                                                   *
    ***********************************************************************/
    {
        return (str.indexOf(":") != -1) || (str.indexOf("/") != -1) || (str.indexOf("\\") != -1);
    }

    private static void CommandLineError(String msg)
    /*********************************************************************
    * Announce a command line error with the string indicating the       *
    * explanation, write the help message, and halt.                     *
    *********************************************************************/
    {
        ToolIO.out.println("TLATeX command-line error: " + msg + ".");
        ToolIO.out.println("Use -help option for more information.");
        // OutputMessageFile(Parameters.HelpFile) ;
        throw new TLA2TexException("TLATeX command-line error: " + msg + "." + "Use -help option for more information.");
    }

    private static void OutputMessageFile(String fileName)
    /**********************************************************************
    * Write the resource file named fileName to stdout.                   *
    **********************************************************************/
    {
        ResourceFileReader input = new ResourceFileReader(fileName);
        String line = input.getLine();
        while (line != null)
        {
            ToolIO.out.println(line);
            line = input.getLine();
        }
        ;
        input.close();
    };

    private static long start = Debug.now();

    /***********************************************************************
    * Starting / Finished used to print debugging information.            *
    ***********************************************************************/
    private static void Starting(String name)
    {
        if (Parameters.Debug)
        {
            start = Debug.now();
            ToolIO.out.println("Starting " + name);
        }
    }

    private static void Finished(String name)
    {
        if (Parameters.Debug)
        {
            Debug.printElapsedTime(start, name + " finished in");
        }
    }

    private static void MakePSFile()
    {
        String Command = Parameters.PSCommand + " " + Parameters.LaTeXOutputFile + ".dvi";
        ExecuteCommand.executeCommand(Command);
        /*******************************************************************
        * Modified on 11 November 2001 to call ExecuteCommand.             *
        *******************************************************************/
    }
}
