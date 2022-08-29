// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
 * CLASS TeX                                                                *
 *                                                                          *
 * THINGS TO DO:                                                            *
 *  - Change parameters.latexwidth to be a float.  This requires            *
 *    rewriting a bunch of code.  (Should do parameters.latexheight as      *
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
 *    parameters.WordFile                                                   *
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
package tla2tex;

import util.ToolIO;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Objects;

class TeX {                                            // BEGIN class


    static final String lastModified =
            /***********************************************************************
             * The following string is inserted by an Emacs macro when a new        *
             * version is saved.                                                    *
             ***********************************************************************/
            "last modified on Wed 12 Apr 2013 at 16:08:49 PST by lamport";

    static final String modDate = lastModified.substring(21, 33);
    /***********************************************************************
     * The modification date.                                               *
     ***********************************************************************/

    static final String version =
            "tla2tex.TeX Version 1.0 created " + modDate;
    private static long start = Debug.now();

    public static void main(final String[] args) {
        Parameters parameters = new Parameters();
        TokenizeSpec tokenizeSpec = new TokenizeSpec(parameters);

        /*********************************************************************
         * Get the command-line arguments.                                    *
         *********************************************************************/
        final long startTime = Debug.now();
        ToolIO.out.println(version);
        GetArguments(parameters, args);

        /*********************************************************************
         * Initialize class BuiltInSymbols.                                   *
         *********************************************************************/
        Starting("BuiltInSymbols.Initialize", parameters);
        BuiltInSymbols.Initialize();
        Finished("BuiltInSymbols.Initialize", parameters);

        /*********************************************************************
         * Initialize class FormatComments.                                   *
         *********************************************************************/
        Starting("FormatComments.Initialize", parameters);
        FormatComments formatComments = new FormatComments(tokenizeSpec);
        formatComments.Initialize();
        Finished("FormatComments.Initialize", parameters);

        /*********************************************************************
         * Obtain the linewidths from the log file.                           *
         *********************************************************************/
        final float[] lineWidths = ReadLogFile(parameters);

        /*********************************************************************
         * Open the input and output files.                                   *
         *********************************************************************/
        BufferedReader infile = null;
        try {
            infile = new BufferedReader(new FileReader(parameters.TLAInputFile));
        } catch (final Exception e) {
            Debug.ReportError(
                    "Can't open input file " + parameters.TLAInputFile);
        }

        OutputFileWriter outfile = null;
        try {
            outfile = new OutputFileWriter(parameters.LaTeXOutputFile + ".new");
        } catch (final Exception e) {
            Debug.ReportError(
                    "Can't open output file " + parameters.LaTeXOutputFile + ".new");
        }

        int lineNum = 0;
        /*******************************************************************
         * The number of lines read from the input file.                    *
         *******************************************************************/

        /*********************************************************************
         * Copy the preamble (everything through the line containing          *
         * \begin{document}, and save everything except the                   *
         * \begin{document} in the ArrayList preamble.                           *
         *********************************************************************/
        final ArrayList<String> preamble = new ArrayList<>(200);
        String line = "";
        try {
            line = Objects.requireNonNull(infile).readLine();
            while ((line != null)
                    && (!line.contains("\\begin{document}"))) {
                lineNum = lineNum + 1;
                Objects.requireNonNull(outfile).putLine(line);
                preamble.add(line);
                line = infile.readLine();
            }
        } catch (final Exception e) {
            Debug.ReportError("I/O error: " + e.getMessage());
        }
        if (line == null) {
            Debug.ReportError("Input file has no \\begin{document}");
        }
        lineNum = lineNum + 1;

        /*********************************************************************
         * Write out the \begin{document} line                                *
         *********************************************************************/
        Objects.requireNonNull(outfile).putLine(line);


        /*********************************************************************
         * If there's something before the \begin{document} on the line, add  *
         * it to preamble.                                                    *
         *********************************************************************/
        final int begindocPos = Objects.requireNonNull(line).indexOf("\\begin{document}");
        if (begindocPos != 0) {
            preamble.add(line.substring(0, begindocPos));
        }

        /*********************************************************************
         * Process the body of the input file.                                *
         *********************************************************************/
        try {
            line = infile.readLine();
            int envNum = 0;
            /****************************************************************
             * The number of tla, pcal, or ppcal environments processed so   *
             * far.                                                          *
             ****************************************************************/

            while (line != null) {                                   // BEGIN while (line != null)
                lineNum = lineNum + 1;
                outfile.putLine(line);

                /*
                 * If this line begins a tla, pcal, or ppcal environment, set
                 * mode to the correct mode for calling TokenizeSpec and set
                 * envName to "tla", "pcal", or "ppcal"
                 */
                int mode = -1;
                String envName = "";
                if (line.contains("\\begin{tla}")) {
                    mode = tokenizeSpec.TLA;
                    envName = "tla";
                } else if (line.contains("\\begin{pcal}")) {
                    mode = tokenizeSpec.PLUSCAL;
                    envName = "pcal";
                } else if (line.contains("\\begin{ppcal}")) {
                    mode = tokenizeSpec.P_PLUSCAL;
                    envName = "ppcal";
                }
                if (mode != -1) {        // BEGIN then OF if (mode != -1)
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
                            + " on line " + (lineNum + 1), parameters);
                    final ArrayList<String> tla = new ArrayList<>(100);
                    final int tlaLineNum = lineNum;
                    line = infile.readLine();
                    while ((line != null)
                            && (!line.contains("\\end{" + envName + "}"))) {
                        lineNum = lineNum + 1;
                        outfile.putLine(line);
                        tla.add(line);
                        line = infile.readLine();
                    }

                    if (line == null) {
                        Debug.ReportError("Unmatched \\begin{" + envName + "} on line "
                                + (tlaLineNum + 1));
                    }
                    lineNum = lineNum + 1;

                    /**************************************************************
                     * Write out the \end{tla} line                                *
                     **************************************************************/
                    outfile.putLine(line);

                    /**************************************************************
                     * Read next line, reporting an error if there is none.        *
                     **************************************************************/
                    line = infile.readLine();
                    if (line == null) {
                        Debug.ReportError("Missing \\end{document}");
                    }

                    /**************************************************************
                     * If next line begins a tlatex environment, then skip over    *
                     * that environment and read the line beyond it.               *
                     **************************************************************/
                    if (Objects.requireNonNull(line).contains("\\begin{tlatex}")) {
                        lineNum = lineNum + 1;
                        line = infile.readLine();
                        while ((line != null)
                                && (!line.contains("\\end{tlatex}"))) {
                            lineNum = lineNum + 1;
                            line = infile.readLine();
                        }
                        if (line == null) {
                            Debug.ReportError("Unmatched \\begin{tlatex} on line "
                                    + (tlaLineNum + tla.size() + 2));
                        }
                        lineNum = lineNum + 1;
                        line = infile.readLine();

                    }

                    /***************************************************************
                     * Tokenize the spec.                                           *
                     ***************************************************************/
                    final CharReader tlaRdr = new VectorCharReader(tla, tlaLineNum);
                    final Token[][] spec = tokenizeSpec.Tokenize(tlaRdr, mode);

                    /***************************************************************
                     * Finish the tokenization by converting sequences of tokens    *
                     * that represent proof-step numbers to PF_STEP tokens.         *
                     ***************************************************************/
                    Token.FindPfStepTokens(spec);

                    /*********************************************************************
                     * Really finish the tokenization by parentheses and braces that are  *
                     * part of the PlusCal C-syntax to tokens that are printed            *
                     * appropriately.                                                     *
                     *********************************************************************/
                    tokenizeSpec.FixPlusCal(spec, true);

                    /***************************************************************
                     * Process the comment tokens.                                  *
                     ***************************************************************/
                    CommentToken.ProcessComments(spec);

                    /***************************************************************
                     * Add the alignment pointers to spec.                          *
                     ***************************************************************/
                    FindAlignments.FindAlignments(spec, tokenizeSpec);
                    // Debug.print2DArray(spec, "spec");

                    /***************************************************************
                     * Find the linewidth for this tla/pcal/ppcal environment.      *
                     ***************************************************************/
                    float linewidth = -1;
                    if (envNum < lineWidths.length) {
                        linewidth = lineWidths[envNum];
                    } else {
                        if (envNum == lineWidths.length) {
                            ToolIO.out.println(
                                    "More tla/pcal/ppcal environments than the last time file\n"
                                            + "    run through LaTeX");
                        }
                    }

                    /***************************************************************
                     * Set the LaTeXtextwidth parameter.  This parameter should     *
                     * probably be changed to a float, but hopefully doing things   *
                     * to the nearest point is good enough.                         *
                     ***************************************************************/
                    parameters.LaTeXtextwidth = (int) linewidth;
                    LaTeXOutput latexOutput = new LaTeXOutput(formatComments);
                    /***************************************************************
                     * Write the alignment file, run it through LaTeX, and set the  *
                     * dimension information in spec based on the log file          *
                     * produced by LaTeX.                                           *
                     ***************************************************************/
                    latexOutput.WriteTeXAlignmentFile(spec, preamble, linewidth);
                    Starting("to LaTeX alignment file.", parameters);
                    latexOutput.RunLaTeX(parameters.LaTeXAlignmentFile);
                    Finished("LaTeXing alignment file", parameters);
                    latexOutput.SetDimensions(spec);
                    // Debug.print2DArray(spec, "");

                    /***************************************************************
                     * Write the tlatex environment.                                *
                     ***************************************************************/
                    latexOutput.WriteTLATeXEnvironment(spec, outfile);
                    Finished("tla/pcal/ppcal environment number " + (envNum + 1), parameters);
                    envNum = envNum + 1;
                }  // END then OF if (mode != -1)
                else {/**************************************************************
                 * This line did not begin a tla, pcal, or ppcal environment.  *
                 **************************************************************/
                    line = infile.readLine();
                }
            }                                  // END while (line != null)
            if (envNum < lineWidths.length) {
                ToolIO.out.println(
                        "Fewer tla/pcal/ppcal environments than the last time file\n"
                                + "    run through LaTeX");
            }
            /*******************************************************************
             * Close and rename the files.                                      *
             *******************************************************************/
            infile.close();
            outfile.close();
            final File iFile = new File(parameters.LaTeXOutputFile + ".tex");
            final File oFile = new File(parameters.LaTeXOutputFile + ".new");

            /*******************************************************************
             * Delete the old version of the .old file, if there is one.        *
             *******************************************************************/
            (new File(parameters.LaTeXOutputFile + ".old")).delete();

            if (!iFile.renameTo(new File(parameters.LaTeXOutputFile + ".old"))
                    || !oFile.renameTo(new File(parameters.LaTeXOutputFile + ".tex"))) {
                Debug.ReportError("Error while renaming files");
            }
        } catch (final Exception e) {
            Debug.ReportError("I/O error: " + e.getMessage());
        }

        Debug.printElapsedTime(startTime, "Total execution time:");
    }  // END main

    private static void GetArguments(final Parameters parameters, final String[] args)
    /**********************************************************************
     * Get the command-line arguments and set the appropriate parameters.  *
     **********************************************************************/
    { /********************************************************************
     * The following flags are set if the indicated option is present.   *
     ********************************************************************/
        boolean outOption = false;
        boolean alignOutOption = false;
        final boolean psOption = false;
        final boolean nopsOption = false;
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

        if ((args[maxArg].length() != 0)
                && (args[maxArg].charAt(0) == '-'))
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
                    OutputMessageFile(parameters.TeXHelpFile);
                    System.exit(0);
                }
                case "-info" -> {
                    OutputMessageFile(parameters.TeXInfoFile);
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
                case "-latexCommand" -> {
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXCommand = args[nextArg];
                }
                case "-out" -> {  /*************************************************************
                 * The LaTeX output file.                                     *
                 *************************************************************/
                    outOption = true;
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXOutputFile = RemoveExtension(args[nextArg]);
                    if (HasPathPrefix(parameters.LaTeXOutputFile)) {
                        CommandLineError(
                                "-out file contains a path specifier.\n"
                                        + "It must be a file in the current directory.");
                    }
                }
                case "-alignOut" -> {  /*************************************************************
                 * The alignment file.  The default is "tlatex".              *
                 *************************************************************/
                    alignOutOption = true;
                    nextArg = nextArg + 1;
                    if (nextArg >= args.length) {
                        CommandLineError("No input file specified");
                    }
                    parameters.LaTeXAlignmentFile = RemoveExtension(args[nextArg]);
                    if (HasPathPrefix(parameters.LaTeXAlignmentFile)) {
                        CommandLineError(
                                "-alignOut file contains a path specifier.\n"
                                        + "It must be a file in the current directory.");
                    }
                }
                case "-debug" -> parameters.Debug = true;

// Should probably change the way the -number option is implemented
// so numbering is controlled by a LaTeX command, so the user
// of tlatex.TeX can get lines numbered.
//
//          else if (option.equals("-number"))
                default -> CommandLineError("Unknown option: " + option);
            }
            nextArg = nextArg + 1;
        }                      // END while (nextArg < maxArg)

        if (nextArg > maxArg)
        /******************************************************************
         * The last option took an argument that was the last              *
         * command-line argument.                                          *
         ******************************************************************/ {
            CommandLineError("No input file specified");
        }

        /********************************************************************
         * Set parameters.TLAInputFile to the last argument, adding ".tex"   *
         * if it has no extension already.                                   *
         ********************************************************************/
        if (!args[maxArg].contains(".")) {
            parameters.TLAInputFile = args[maxArg] + ".tex";
        } else {
            parameters.TLAInputFile = args[maxArg];
        }

        /********************************************************************
         * Set default options.                                              *
         ********************************************************************/
        if (!outOption) {
            parameters.LaTeXOutputFile =
                    RemoveExtension(RemovePathPrefix(parameters.TLAInputFile));
            if (HasPathPrefix(parameters.TLAInputFile))
                ToolIO.out.println(
                        "Warning: Output file being written to a different directory\n"
                                + "         than input file.");
        }
        if (!alignOutOption) {
            parameters.LaTeXAlignmentFile = "tlatex";
        }

        /********************************************************************
         * Produce Postscript output if either                               *
         *   (i) -ps, or                                                     *
         *  (ii) -shade but not -nops                                        *
         * was specified.                                                    *
         ********************************************************************/
        if (psOption
                || (parameters.CommentShading && !nopsOption)) {
            parameters.PSOutput = true;
        }
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
        return (str.contains(":"))
                || (str.contains("/"))
                || (str.contains("\\"));
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

    private static float[] ReadLogFile(final Parameters parameters)
    /***********************************************************************
     * Reads the log file to obtain the linewidths for the tla              *
     * environments, and returns them as an array of floats.  Each          *
     * linewidth is written to the log file as a separate line such as      *
     *                   \%{123.456}                                        *
     ***********************************************************************/
    {
        final ArrayList<String> resultVec = new ArrayList<>(50);
        /*******************************************************************
         * A vector of the strings representing the linewidths.             *
         *******************************************************************/

        try (BufferedReader logfile = new BufferedReader(
                new FileReader(parameters.LaTeXOutputFile + ".log"))) {
            String inputLine = logfile.readLine();
            while (inputLine != null) {
                if ((inputLine.startsWith("\\%{"))) {
                    final int start = 3;
                    final int after = inputLine.indexOf("}", start) - 2;
                    resultVec.add(inputLine.substring(start, after));
                }
                inputLine = logfile.readLine();
            }
        } catch (final IOException e) {
            ToolIO.out.println(
                    "No file " + parameters.LaTeXOutputFile + ".log");
            return new float[0];
        } catch (final Exception e) {
            Debug.ReportError(
                    "Error reading file " + parameters.LaTeXOutputFile + ".log");
        }

        final float[] result = new float[resultVec.size()];
        int i = 0;
        while (i < result.length) {
            result[i] = Misc.stringToFloat(resultVec.get(i));
            i = i + 1;
        }
        return result;
    }
}


