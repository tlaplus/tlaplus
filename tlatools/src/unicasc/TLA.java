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
package unicasc;

import tla2tex.BuiltInSymbols;
import tla2tex.CommentToken;
import tla2tex.Debug;
import tla2tex.FileCharReader;
import tla2tex.FindAlignments;
import tla2tex.FormatComments;
import tla2tex.OutputFileWriter;
import tla2tex.ResourceFileReader;
import tla2tex.TLA2TexException;
import tla2tex.Token;
import tla2tex.TokenizeSpec;
import util.ToolIO;

public class TLA {
	static final String lastModified =
			"last modified on Wed  12 Apr 2013 at 16:06:38 PST by lamport";

	static String modDate = lastModified.substring(21, 33);
	// The modification date.

	static String version = "tla2tex.TLA Version 1.0 created " + modDate;

	public static void main(String[] args) {
		runTranslation(args);
	}

	public static void runTranslation(String[] args) {
		// Get the command-line arguments.
		long startTime = Debug.now();
		// ToolIO.out.println(version);
		GetArguments(args);

		// Initialize class BuiltInSymbols
		Starting("BuiltInSymbols.Initialize");
		BuiltInSymbols.Initialize();
		Finished("BuiltInSymbols.Initialize");

		// Read and tokenize the spec.
		FileCharReader testlr = new FileCharReader(Parameters.TLAInputFile);
		Starting("TokenizeSpec.Tokenize");
		final Token[][] spec = TokenizeSpec.Tokenize(testlr, TokenizeSpec.MODULE);

		 // Finish tokenization by converting proof-step numbers to PF_STEP tokens.
		Token.FindPfStepTokens(spec);
		Finished("TokenizeSpec.Tokenize");
		// Debug.print2DArray(spec, "tok");

//		/*********************************************************************
//		 * Really finish the tokenization by parentheses and braces that are
//		 * part of the PlusCal C-syntax to tokens that are printed
//		 * appropriately.
//		 *********************************************************************/
//		Starting("TokenizeSpec.FixPlusCal");
//		TokenizeSpec.FixPlusCal(spec, false);
//		Finished("TokenizeSpec.FixPlusCal");

		// Process the comment tokens. *
		Starting("CommentToken.ProcessComments");
		CommentToken.ProcessComments(spec);
		Finished("CommentToken.ProcessComments");
		// Debug.print2DArray(spec, "com");

		// Initialize class FormatComments
		// pron: ????
		Starting("FormatComments.Initialize");
		FormatComments.Initialize();
		Finished("FormatComments.Initialize");

		// Add the alignment pointers to spec. *
		Starting("FindAlignments.FindAlignments");
		FindAlignments.FindAlignments(spec);
		Finished("FindAlignments.FindAlignments");
		// Debug.print2DArray(spec, "align");

		// Write output
		Starting("LaTeXOutput.WriteAlignmentFile");
		A2U.a2u(spec, new OutputFileWriter(System.out, "STDOUT"));
		Finished("LaTeXOutput.WriteAlignmentFile");

		Debug.printElapsedTime(startTime, "Total execution time:");
	}

	private static void GetArguments(String[] args) {
		/**********************************************************************
		 * Get the command-line arguments and set the appropriate parameters.
		 **********************************************************************/

		/********************************************************************
		 * The following flags are set if the indicated option is present.
		 ********************************************************************/
		boolean outOption = false;

		int nextArg = 0; // The number of the argument being processed.
		int maxArg = args.length - 1; // The number of the final argument, the input file name.
		if (maxArg < 0)
			CommandLineError("No arguments specified");

		/******************************************************************
		 * If the last argument begins with "-", then no file has been
		 * specified. This should mean that the user has typed "-help" or
		 * "-info", but it could be another mistake.
		 ******************************************************************/
		if ((args[maxArg].length() != 0) && (args[maxArg].charAt(0) == '-'))
			maxArg = maxArg + 1;

		while (nextArg < maxArg) {
			// Process all the arguments, except for the last (unless it's a "-" argument). *
			String option = args[nextArg];
			if (option.equals("-help")) {
				OutputMessageFile(Parameters.HelpFile);
				System.exit(0);
			} else if (option.equals("-info")) {
				OutputMessageFile(Parameters.InfoFile);
				System.exit(0);
			} else if (option.equals("-out")) {
				// The LaTeX output file.
				outOption = true;
				nextArg = nextArg + 1;
				if (nextArg >= args.length)
					CommandLineError("No input file specified");

				Parameters.LaTeXOutputFile = RemoveExtension(args[nextArg]);
				if (HasPathPrefix(Parameters.LaTeXOutputFile)) {
					CommandLineError(
							"-out file contains a path specifier.\n" + "It must be a file in the current directory.");
				}
			} else if (option.equals("-tlaOut")) {
				Parameters.TLAOut = true;
				nextArg = nextArg + 1;
				if (nextArg >= args.length)
					CommandLineError("No input file specified");

				Parameters.TLAOutFile = args[nextArg];
				if (Parameters.TLAOutFile.indexOf(".") == -1)
					Parameters.TLAOutFile = Parameters.TLAOutFile + ".tla";

				if (HasPathPrefix(Parameters.TLAOutFile))
					CommandLineError("-tlaOut file contains a path specifier.\n"
							+ "It must be a file in the current directory.");

			} else if (option.equals("-debug"))
				Parameters.Debug = true;
			else
				CommandLineError("Unknown option: " + option);

			nextArg = nextArg + 1;
		}

		if (nextArg > maxArg) {
			// The last option took an argument that was the last command-line argument.
			CommandLineError("No input file specified");
		}

		/********************************************************************
		 * Set Parameters.TLAInputFile to the last argument, adding ".tla" * if
		 * it has no extension already. *
		 ********************************************************************/
		if (args[maxArg].indexOf(".") == -1)
			Parameters.TLAInputFile = args[maxArg] + ".tla";
		else
			Parameters.TLAInputFile = args[maxArg];

		// Report an error if TLAInputFile = TLAOutFile. *
		if (Parameters.TLAOutFile.equals(Parameters.TLAInputFile))
			CommandLineError("\n  -tlaOut file the same as the tla input file.\n"
					+ "  This would overwrite your input file, so I won't do it");

		// Set default options.
		if (!outOption)
			Parameters.LaTeXOutputFile = RemoveExtension(RemovePathPrefix(Parameters.TLAInputFile));
	}

	private static String RemoveExtension(String fileName) {
		// The string fileName with any extensions removed.
		if (fileName.indexOf(".") == -1)
			return fileName;
		else
			return fileName.substring(0, fileName.indexOf("."));
	}

	private static String RemovePathPrefix(String str) {
	/***********************************************************************
	 * Returns str with all any leading path specifiers removed. For * example,
	 * calling it on "c:frob\bar\name.txt" or "~/frob/bar/name.txt" * will
	 * return "name.txt". *
	 ***********************************************************************/
		String result = str;
		if (result.indexOf(":") != -1)
			result = result.substring(result.lastIndexOf(":") + 1);
		if (result.indexOf("/") != -1)
			result = result.substring(result.lastIndexOf("/") + 1);
		if (result.indexOf("\\") != -1)
			result = result.substring(result.lastIndexOf("\\") + 1);
		return result;
	}

	private static boolean HasPathPrefix(String str) {
		// True iff str has a leading path specifier--that is, if it contains a ":", "/" or "\".
		return (str.indexOf(":") != -1) || (str.indexOf("/") != -1) || (str.indexOf("\\") != -1);
	}

	private static void CommandLineError(String msg) {
		// Announce a command line error, write the help message, and halt.
		ToolIO.out.println("TLATeX command-line error: " + msg + ".");
		ToolIO.out.println("Use -help option for more information.");
		// OutputMessageFile(Parameters.HelpFile) ;
		throw new TLA2TexException(
				"TLATeX command-line error: " + msg + "." + "Use -help option for more information.");
	}

	private static void OutputMessageFile(String fileName) {
		// Write the resource file named fileName to stdout. *
		ResourceFileReader input = new ResourceFileReader(fileName);
		String line = input.getLine();
		while (line != null) {
			ToolIO.out.println(line);
			line = input.getLine();
		}

		input.close();
	}

	private static long start = Debug.now();

	// Starting / Finished used to print debugging information.
	private static void Starting(String name) {
		if (Parameters.Debug) {
			start = Debug.now();
			ToolIO.out.println("Starting " + name);
		}
	}

	private static void Finished(String name) {
		if (Parameters.Debug)
			Debug.printElapsedTime(start, name + " finished in");
	}
}
