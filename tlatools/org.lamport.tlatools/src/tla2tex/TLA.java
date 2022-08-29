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
 *    parameters.WordFile                                                   *
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
 * latexOutput.WriteAlignmentFile                                           *
 *    Writes the -alignOut file.                                            *
 *                                                                          *
 * latexOutput.RunLaTeX                                                     *
 *    Runs LaTeX on the -alignOut file.  This aux file produced by LaTeX    *
 *    contains the information about the typeset widths of text that        *
 *    TLATeX needs to perform the alignment.                                *
 *                                                                          *
 * latexOutput.SetDimensions                                                *
 *    Reads the LaTeX aux file and determines how much space it needs to    *
 *    add for alignment, setting the information in the tokens'             *
 *    distFromMargin and preSpace fields.                                   *
 *                                                                          *
 * latexOutput.WriteLaTeXFile                                               *
 *    Writes the -out file, containing LaTeX input to produce the           *
 *    typeset version.                                                      *
 *                                                                          *
 * latexOutput.RunLaTeX                                                     *
 *    Runs LaTeX on the -out file.                                          *
 *                                                                          *
 * MakePSFile                                                               *
 *    If the appropriate options are chosen, it runs the -psCommand         *
 *    command on the dvi file produced by LaTeX to produce a Postscript     *
 *    or pdf file.                                                          *
 ***************************************************************************/
package tla2tex;

import util.FileUtil;
import util.TLAConstants;
import util.ToolIO;

import java.io.File;
import java.io.IOException;

public class TLA {
    static final String lastModified =
            /***********************************************************************
             * The following string is inserted by an Emacs macro when a new        *
             * version is saved.                                                    *
             ***********************************************************************/
            "last modified on Wed  12 Apr 2013 at 16:06:38 PST by lamport";

    static final String modDate = lastModified.substring(21, 33);
    /***********************************************************************
     * The modification date.                                               *
     ***********************************************************************/

    static final String version = "tla2tex.TLA Version 1.0 created " + modDate;
    private static long start = Debug.now();

    public static void main(final String[] args) {
        runTranslation(args);
    }

    /**
     *
     */
    public static void runTranslation(final String[] args) {

        Parameters parameters = new Parameters();
        TokenizeSpec tokenizeSpec = new TokenizeSpec(parameters);

        /*********************************************************************
         * Get the command-line arguments.                                    *
         *********************************************************************/
        final long startTime = Debug.now();
        ToolIO.out.println(version);
        GetArguments(args, parameters);

        /*********************************************************************
         * Initialize class BuiltInSymbols.                                   *
         *********************************************************************/
        Starting("BuiltInSymbols.Initialize", parameters);
        BuiltInSymbols.Initialize();
        Finished("BuiltInSymbols.Initialize", parameters);


        /*********************************************************************
         * Read and tokenize the spec.                                        *
         *********************************************************************/
        final FileCharReader testlr = new FileCharReader(parameters.TLAInputFile);
        Starting("TokenizeSpec.Tokenize", parameters);
        final Token[][] spec = tokenizeSpec.Tokenize(testlr, tokenizeSpec.MODULE);

/*********************************************************************
 * Finish the tokenization by converting sequences of tokens that     *
 * represent proof-step numbers to PF_STEP tokens.                    *
 *********************************************************************/
        Token.FindPfStepTokens(spec);
        Finished("TokenizeSpec.Tokenize", parameters);
        // Debug.print2DArray(spec, "tok");

        /*********************************************************************
         * Really finish the tokenization by parentheses and braces that are  *
         * part of the PlusCal C-syntax to tokens that are printed            *
         * appropriately.                                                     *
         *********************************************************************/
        Starting("TokenizeSpec.FixPlusCal", parameters);
        tokenizeSpec.FixPlusCal(spec, false);
        Finished("tokenizeSpec.FixPlusCal", parameters);

        /*********************************************************************
         * Process the comment tokens.                                        *
         *********************************************************************/
        Starting("CommentToken.ProcessComments", parameters);
        CommentToken.ProcessComments(spec);
        Finished("CommentToken.ProcessComments", parameters);
        // Debug.print2DArray(spec, "com");

        /*********************************************************************
         * Initialize class FormatComments.                                   *
         *********************************************************************/
        Starting("FormatComments.Initialize", parameters);
        FormatComments formatComments = new FormatComments(tokenizeSpec);
        formatComments.Initialize();
        Finished("FormatComments.Initialize", parameters);

        /*********************************************************************
         * Add the alignment pointers to spec.                                *
         *********************************************************************/
        Starting("FindAlignments.FindAlignments", parameters);
        FindAlignments.FindAlignments(spec, tokenizeSpec);
        Finished("FindAlignments.FindAlignments", parameters);
        // Debug.print2DArray(spec, "align");

        /*********************************************************************
         * Write out the tla file with deleted comments removed, if the       *
         * -tlaOut option is chosen.                                          *
         *********************************************************************/
        if (parameters.TLAOut) {
            WriteTLAFile.Write(spec, parameters.TLAOutFile);
            ToolIO.out.println("Wrote -tlaOut file " + parameters.TLAOutFile);
        }

        /*********************************************************************
         * Write the alignment file, run it through LaTeX, and set the        *
         * dimension information in spec based on the log file produced by    *
         * LaTeX.                                                             *
         *********************************************************************/
        LaTeXOutput latexOutput = new LaTeXOutput(formatComments);

        Starting("latexOutput.WriteAlignmentFile", parameters);
        latexOutput.WriteAlignmentFile(spec);
        Finished("latexOutput.WriteAlignmentFile", parameters);

        Starting("latexOutput.RunLaTeX", parameters);
        latexOutput.RunLaTeX(parameters.LaTeXAlignmentFile);
        Finished("latexOutput.RunLaTeX", parameters);

        Starting("latexOutput.SetDimensions", parameters);
        latexOutput.SetDimensions(spec);
        Finished("latexOutput.SetDimensions", parameters);
        // Debug.print2DArray(spec, "");

        /*********************************************************************
         * Write the final LaTeX output and run it through LaTeX.             *
         *********************************************************************/
        Starting("latexOutput.WriteLaTeXFile", parameters);
        latexOutput.WriteLaTeXFile(spec);
        Finished("latexOutput.WriteLaTeXFile", parameters);

        Starting("latexOutput.RunLaTeX", parameters);
        latexOutput.RunLaTeX(parameters.LaTeXOutputFile);
        Finished("latexOutput.RunLaTeX", parameters);

        ToolIO.out.println("TLATeX " + parameters.LatexOutputExt + " output written on " +
                parameters.LaTeXOutputFile + "." +
                parameters.LatexOutputExt +
                ((parameters.MetaDir.equals("")) ? "" : ", from " + parameters.MetaDir) + ".");

        if (parameters.PSOutput) {
            /******************************************************************
             * Produce the Postscript file.                                    *
             ******************************************************************/
            Starting("MakePSFile", parameters);
            MakePSFile(parameters);
            Finished("MakePSFile", parameters);
            ToolIO.out.println("TLATeX Postscript (or pdf) output written on " + parameters.LaTeXOutputFile
                    + ".ps (or " + parameters.LaTeXOutputFile + ".pdf).");
        }
        if (!parameters.MetaDir.equals("")) {
            try {
                FileUtil.copyFile(latexOutput.prependMetaDirToFileName(parameters.LaTeXOutputFile + "."
                        + parameters.LatexOutputExt), parameters.TLAInputFile.substring(0, parameters.TLAInputFile
                        .length()
                        - "tla".length())
                        + parameters.LatexOutputExt);
            } catch (final IOException e) {
                Debug.ReportError("Trying to copy output from metadir produced the error:\n" + e.getMessage());
            }

        }
        Debug.printElapsedTime(startTime, "Total execution time:");
    } // END main

    private static void GetArguments(final String[] args, Parameters parameters)
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
        parameters.CommentShading = false;
        parameters.PrintLineNumbers = false;

        int nextArg = 0;
        /******************************************************************
         * The number of the argument being processed.                     *
         ******************************************************************/
        int maxArg = args.length - 1;
        /******************************************************************
         * The number of the final argument, which is the input file name. *
         ******************************************************************/
        if (maxArg < 0) {
            CommandLineError("No arguments specified");
        }

        if ((args[maxArg].length() != 0) && (args[maxArg].charAt(0) == '-'))
        /******************************************************************
         * If the last argument begins with "-", then no file has been     *
         * specified.  This should mean that the user has typed "-help"    *
         * or "-info", but it could be another mistake.                    *
         ******************************************************************/ {
            maxArg = maxArg + 1;
        }

        while (nextArg < maxArg)
        /*******************************************************************
         * Process all the arguments, except for the last (unless it's a    *
         * "-" argument).                                                   *
         *******************************************************************/ {
            final String option = args[nextArg];
            switch (option) {
                case "-help" -> {
                    OutputMessageFile(parameters.HelpFile);
                    System.exit(0);
                }
                case "-info" -> {
                    OutputMessageFile(parameters.InfoFile);
                    System.exit(0);
                }
                case "-grayLevel" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    try {
                        parameters.PSGrayLevel = Misc.stringToFloat(args[nextArg]);
                    } catch (final Exception e) {
                        CommandLineError("Bad -grayLevel value " + args[nextArg]);
                    }
                    // bug found by Yuan Yu in following if statement
                    // corrected 9 May 2001
                    if ((parameters.PSGrayLevel > 1) || (parameters.PSGrayLevel < 0)) {
                        CommandLineError("-grayLevel value should be between 0 and 1, not "
                                + Misc.floatToString(parameters.PSGrayLevel, 3));
                    }
                }
                case "-ps" -> psOption = true;
                case "-nops" -> nopsOption = true;
                case "-psCommand" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.PSCommand = args[nextArg];
                }
                case "-latexCommand" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXCommand = args[nextArg];
                }
                case "-out" -> {
                    /*************************************************************
                     * The LaTeX output file.                                     *
                     *************************************************************/
                    outOption = true;
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXOutputFile = RemoveExtension(args[nextArg]);
                    if (HasPathPrefix(parameters.LaTeXOutputFile)) {
                        CommandLineError("-out file contains a path specifier.\n"
                                + "It must be a file in the current directory.");
                    }
                }
                case "-tlaOut" -> {
                    /*************************************************************
                     * The tla output file, with TEX comments removed.  Add a     *
                     * ".tla" extension if no extension is specified.             *
                     *************************************************************/
                    parameters.TLAOut = true;
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.TLAOutFile = args[nextArg];
                    if (!parameters.TLAOutFile.contains(".")) {
                        parameters.TLAOutFile = parameters.TLAOutFile + TLAConstants.Files.TLA_EXTENSION;
                    }
                    if (HasPathPrefix(parameters.TLAOutFile)) {
                        CommandLineError("-tlaOut file contains a path specifier.\n"
                                + "It must be a file in the current directory.");
                    }
                }
                case "-alignOut" -> {
                    /*************************************************************
                     * The alignment file.                                        *
                     *************************************************************/
                    alignOutOption = true;
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXAlignmentFile = RemoveExtension(args[nextArg]);
                    if (HasPathPrefix(parameters.LaTeXAlignmentFile)) {
                        CommandLineError("-alignOut file contains a path specifier.\n"
                                + "It must be a file in the current directory.");
                    }
                }
                case "-debug" -> parameters.Debug = true;
                case "-tlaComment" ->
                /***************************************************************
                 * This option tells TLATeX to interpret all ambiguous          *
                 * identifiers in comments as TLA symbols.                      *
                 ***************************************************************/

                        parameters.TLACommentOption = true;

                // else if (option.equals("-notlaComment"))
                case "-shade" -> parameters.CommentShading = true;
                case "-noPcalShade" -> parameters.NoPlusCalShading = true;
                case "-noProlog" -> parameters.PrintProlog = false;
                case "-noEpilog" -> parameters.PrintEpilog = false;
                case "-number" -> parameters.PrintLineNumbers = true;
                case "-style" -> {
                    /*************************************************************
                     * Use the specified file as style file in place of           *
                     * parameters.LaTeXModuleProlog.                              *
                     *************************************************************/
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.UserStyleFile = RemoveExtension(args[nextArg]);
                    if ((!parameters.UserStyleFile.equals(args[nextArg]))
                            && (args[nextArg].indexOf(".sty") != args[nextArg].length() - 4)) {
                        CommandLineError("-style file must have extension `.sty'");
                    }
                }
                case "-ptSize" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXptSize = GetIntArg(args[nextArg], option);
                    if ((parameters.LaTeXptSize < 10) || (parameters.LaTeXptSize > 12)) {
                        CommandLineError("-ptSize option must be 10, 11, or 12");
                    }
                }
                case "-textwidth" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXtextwidth = GetIntArg(args[nextArg], option);
                    if ((parameters.LaTeXtextwidth < 100) || (parameters.LaTeXtextwidth > 1000)) {
                        CommandLineError("-textwidth value of " + parameters.LaTeXtextwidth + " points is implausible");
                    }
                }
                case "-textheight" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXtextheight = GetIntArg(args[nextArg], option);
                    if ((parameters.LaTeXtextheight < 75) || (parameters.LaTeXtextheight > 1500)) {
                        CommandLineError("-textheight value of " + parameters.LaTeXtextheight + " points is implausible");
                    }
                }
                case "-hoffset" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXhoffset = GetIntArg(args[nextArg], option);
                    if ((parameters.LaTeXhoffset < -250) || (parameters.LaTeXhoffset > 250)) {
                        CommandLineError("-hoffset value of " + parameters.LaTeXhoffset + " points is implausible");
                    }
                }
                case "-voffset" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXvoffset = GetIntArg(args[nextArg], option);
                    if ((parameters.LaTeXvoffset < -250) || (parameters.LaTeXvoffset > 250)) {
                        CommandLineError("-voffset value of " + parameters.LaTeXvoffset + " points is implausible");
                    }
                }
                case "-metadir" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.MetaDir = args[nextArg];
                    parameters.ParentDir = new File(parameters.MetaDir);
                    if (!parameters.ParentDir.exists()) {
                        CommandLineError("Specified metdir " + parameters.MetaDir +
                                " does not exist.");
                    }
                }
                case "-latexOutputExt" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LatexOutputExt = args[nextArg];
                }
                default -> CommandLineError("Unknown option: " + option);
            }
            nextArg = nextArg + 1;
        } // END while (nextArg < maxArg)

        if (nextArg > maxArg)
        /******************************************************************
         * The last option took an argument that was the last              *
         * command-line argument.                                          *
         ******************************************************************/ {
            CommandLineError("No input file specified");
        }

        /********************************************************************
         * Set parameters.TLAInputFile to the last argument, adding ".tla"   *
         * if it has no extension already.                                   *
         ********************************************************************/
        if (!args[maxArg].contains(".")) {
            parameters.TLAInputFile = args[maxArg] + TLAConstants.Files.TLA_EXTENSION;
        } else {
            parameters.TLAInputFile = args[maxArg];
        }

        /********************************************************************
         * Report an error if TLAInputFile = TLAOutFile.                     *
         ********************************************************************/
        if (parameters.TLAOutFile.equals(parameters.TLAInputFile)) {
            CommandLineError("""

                    -tlaOut file the same as the tla input file.
                    This would overwrite your input file, so I won't do it""".indent(2));
        }

        /********************************************************************
         * Set default options.                                              *
         ********************************************************************/
        if (!outOption) {
            parameters.LaTeXOutputFile = RemoveExtension(RemovePathPrefix(parameters.TLAInputFile));
        }
        if (!alignOutOption) {
            parameters.LaTeXAlignmentFile = parameters.LaTeXOutputFile;
        }

        /********************************************************************
         * Produce Postscript output if either                               *
         *   (i) -ps, or                                                     *
         *  (ii) -shade but not -nops                                        *
         * was specified.                                                    *
         ********************************************************************/
        if (psOption || (parameters.CommentShading && !nopsOption)) {
            parameters.PSOutput = true;
        }
    }

    private static int GetIntArg(final String str, final String option)
    /*********************************************************************
     * Returns str interpreted as an integer, or generates an error       *
     * message for the indicated option.                                  *
     *********************************************************************/
    {
        int val = 0;
        try {
            val = Integer.parseInt(str);
        } catch (final NumberFormatException e) {
            CommandLineError(option + " option must specify an integer value");
        }
        return val;
    }

    private static String RemoveExtension(final String fileName)
    /*********************************************************************
     * The string fileName with any extensions removed.                   *
     *********************************************************************/
    {
        if (!fileName.contains(".")) {
            return fileName;
        } else {
            return fileName.substring(0, fileName.indexOf("."));
        }
    }

    private static String RemovePathPrefix(final String str)
    /***********************************************************************
     * Returns str with all any leading path specifiers removed.  For       *
     * example, calling it on "c:frob\bar\name.txt" or "~/frob/bar/name.txt"  *
     * will return "name.txt".                                              *
     ***********************************************************************/
    {
        String result = str;
        if (result.contains(":")) {
            result = result.substring(result.lastIndexOf(":") + 1);
        }
        if (result.contains("/")) {
            result = result.substring(result.lastIndexOf("/") + 1);
        }
        if (result.contains("\\")) {
            result = result.substring(result.lastIndexOf("\\") + 1);
        }
        return result;
    }

    private static boolean HasPathPrefix(final String str)
    /***********************************************************************
     * True iff str has a leading path specifier--that is, if it contains   *
     * a ":", "/" or "\".                                                   *
     ***********************************************************************/
    {
        return (str.contains(":")) || (str.contains("/")) || (str.contains("\\"));
    }

    private static void CommandLineError(final String msg)
    /*********************************************************************
     * Announce a command line error with the string indicating the       *
     * explanation, write the help message, and halt.                     *
     *********************************************************************/
    {
        ToolIO.out.println("TLATeX command-line error: " + msg + ".");
        ToolIO.out.println("Use -help option for more information.");
        // OutputMessageFile(parameters.HelpFile) ;
        throw new TLA2TexException("TLATeX command-line error: " + msg + "." + "Use -help option for more information.");
    }

    private static void OutputMessageFile(final String fileName)
    /**********************************************************************
     * Write the resource file named fileName to stdout.                   *
     **********************************************************************/
    {
        final ResourceFileReader input = new ResourceFileReader(fileName);
        String line = input.getLine();
        while (line != null) {
            ToolIO.out.println(line);
            line = input.getLine();
        }
        input.close();
    }

    /***********************************************************************
     * Starting / Finished used to print debugging information.            *
     ***********************************************************************/
    private static void Starting(final String name, final Parameters parameters) {
        if (parameters.Debug) {
            start = Debug.now();
            ToolIO.out.println("Starting " + name);
        }
    }

    private static void Finished(final String name, final Parameters parameters) {
        if (parameters.Debug) {
            Debug.printElapsedTime(start, name + " finished in");
        }
    }

    private static void MakePSFile(final Parameters parameters) {
        final String Command = parameters.PSCommand + " " + parameters.LaTeXOutputFile + ".dvi";
        ExecuteCommand.executeCommand(Command, parameters);
        /*******************************************************************
         * Modified on 11 November 2001 to call ExecuteCommand.             *
         *******************************************************************/
    }
}
