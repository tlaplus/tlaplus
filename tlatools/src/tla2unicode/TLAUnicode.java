// Copyright (c) 2016 Microsoft Corporation.  All rights reserved.

/***************************************************************************
*                                                                          *
* This program converts TLA+ specifications from ASCII to Unicode          * 
* representation and vice-versa.                                           *
*                                                                          *
* When converting to Unicode, symbols in comments are not converted.       *
* When converting to ASCII, symbols in comments are converted char-by-char *
* to ensure no Unicode characters are left in the file.                    *
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
***************************************************************************/
package tla2unicode;

import java.io.InputStream;
import java.io.OutputStream;
import java.io.Reader;
import java.io.Writer;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import tla2tex.BuiltInSymbols;
import tla2tex.CharReader;
import tla2tex.CommentToken;
import tla2tex.Debug;
import tla2tex.FileCharReader;
import tla2tex.FindAlignments;
import tla2tex.InputStreamCharReader;
import tla2tex.OutputFileWriter;
import tla2tex.TLA2TexException;
import tla2tex.Token;
import tla2tex.TokenizeSpec;
import util.ToolIO;

public class TLAUnicode {
	static final String APP = "unicasc.TLAUnicode";
	static final String VERSION = APP + " Version 1.0";
	
	static final String USAGE = "USAGE: java " + APP + " OP input.tla [output.tla]"
			+ "\nOP is -u2a | -a2u to convert from ASCII to Unicode or vice-versa, respectively."
			+ "\nIf the output file isn't specified, the conversion is printed to the standard output.";
	
  	private static boolean debug = false ; // True if the -debug option is chosen.
	
	public static void convert(boolean toU, InputStream input, OutputStream output) {
		convert(toU, new InputStreamCharReader(input), new OutputFileWriter(output, null));
	}
	
	public static void convert(boolean toU, Reader input, Writer output) {
		convert(toU, new InputStreamCharReader(input), new OutputFileWriter(output, null));
	}
	
	public static void convert(boolean toU, Path inFile, Path outFile) {
		final CharReader input = new FileCharReader(inFile.normalize().toAbsolutePath().toString());
		final OutputFileWriter output = new OutputFileWriter(outFile.normalize().toAbsolutePath().toString());
		convert(toU, input, output);
	}
	
	// Main entry point
	public static void convert(boolean toU, CharReader input, OutputFileWriter output) {
		BuiltInSymbols.Initialize(); // Initialize class BuiltInSymbols

		// Read and tokenize the spec.
		final Token[][] spec = TokenizeSpec.Tokenize(input, TokenizeSpec.MODULE);

		Token.FindPfStepTokens(spec); // Convert proof-step numbers to PF_STEP tokens.
		// Debug.print2DArray(spec, "tok");

		CommentToken.ProcessComments(spec); // Process the comment tokens.
		// Debug.print2DArray(spec, "com");

		// As comments aren't converted to U, mistakenly keeping alignment with a comment
		// can break significant alignment, so we align without comments
		final Token[][] noCommentSpec = filterOutComments(spec);
		FindAlignments.FindAlignments(noCommentSpec); // Add the alignment pointers to spec.
		
		Debug.print2DArray(spec, "spec");
		Debug.print2DArray(noCommentSpec, "noCommentSpec");
		
		// Debug.print2DArray(spec, "align");
		
		convert(toU, spec, noCommentSpec, output); // Write output
	}

	private static void convert(boolean toU, Token[][] spec, Token[][] noCommentSpec, OutputFileWriter writer) {
		// This method performs the actual conversion
		
		List<CommentToken> leftComments = null;
		
		for (int line = 0; line < spec.length; line++) {
			final StringBuilder out = new StringBuilder();
			leftComments = new ArrayList<>(); // left comments that we may need to move to the end of the line 
			boolean onlyComments = true; // we've only encountered comment tokens on this line so far
			boolean keepLeftComments = false;
			
			for (int item = 0; item < spec[line].length; item++) {
				final Token tok = spec[line][item];
				// System.out.println("(" + line + ", " + item + "): " + tok); if (item == spec[line].length - 1) System.out.println("$$$$$$$$$");
				
				// if line ends with an open comment or a line comment and we have left comments to move, 
			    // we wait to output the comment.
				if (keepLeftComments && item == spec[line].length - 1 && tok.type == Token.COMMENT) {
					final CommentToken ctok = (CommentToken) tok;
					// append skipped last comment token
					if (ctok.rsubtype == CommentToken.BEGIN_OVERRUN || ctok.rsubtype == CommentToken.LINE)
						continue;
				}
				
				//---- Align token ----
				
				int space = -1; // How much space to leave before the token
				if (tok.aboveAlign.line != -1 && tok.type != Token.COMMENT) {
					// If aligned to a token above -- try to keep alignment
					final Token align = tok.aboveAlign.toToken(noCommentSpec);
					
					// If this token isn't a comment but it's been aligned with a comment
					// try to see if it can be aligned with a higher, non-comment line
					// As comments aren't converted to U, mistakenly keeping alignment with a comment
					// can break significant alignment
//					if (tok.type != Token.COMMENT) {
//						while (align.type == Token.COMMENT && align.aboveAlign.line != -1) {
//							// System.out.println("Fixing alignment of " + tok + " from " + align + " to " + align.aboveAlign.toToken(noCommentSpec));
//							align = align.aboveAlign.toToken(noCommentSpec);
//						}
//					}
					
					if (align.column == tok.column && align.outcolumn >= 0) {
						final int column = out.length();
						space = align.outcolumn - column;
						
						// If we're the first non-comment token, we must align.
						// If we can't, we move all left comments to the end of the line. 
						// We drop them from the output line, and keep them in leftComments.
						if (space < 0 && onlyComments && tok.type != Token.COMMENT) {
							out.delete(0, out.length()); // reset line
							space = align.outcolumn;
							
							keepLeftComments = true;
							for (CommentToken ctok : leftComments)
								ctok.outcolumn = -1;
							
							if (!leftComments.isEmpty() && leftComments.get(0).rsubtype == CommentToken.END_OVERRUN) {
								out.append("*)");
								space -= 2;
							}
						}
					}
				}
				if (space < 0) // If we don't need to or can't align, keep original spacing.
					space = tok.column - (item > 0 ? spec[line][item - 1].column + spec[line][item - 1].getWidth() : 0);
				
				Debug.Assert(space >= 0, tok + (item > 0 ? " :: " + spec[line][item - 1] : ""));
				appendSpaces(out, space);
				
				if (tok.type != Token.COMMENT) {
					onlyComments = false;
					if (!keepLeftComments)
						leftComments = null;
				}
				
				tok.outcolumn = out.length();
				Debug.Assert(toU // The following invariant always holds:
						? tok.outcolumn <= tok.column  // when -> U, token moves to the left  (or not at all)
						: tok.outcolumn >= tok.column, // when -> A, token moves to the right (or not at all)
					tok.toString());

				//----- Output token ----
				
				switch (tok.type) {
				case Token.BUILTIN: {
					// Here we actually convert the symbol
					String alt = toU ? Unicode.a2u(tok.string) : Unicode.u2a(tok.string);
					out.append(alt != null ? alt : tok.string);
					break;
				}
				case Token.NUMBER:
				case Token.IDENT:
				case Token.PCAL_LABEL:
				case Token.DASHES:
				case Token.END_MODULE:
				case Token.PROLOG:
				case Token.EPILOG:
				case Token.PF_STEP:
					out.append(tok.string);
					break;
				case Token.STRING:
					out.append("\"" + tok.string + "\"");
					break;

				case Token.COMMENT:
					final CommentToken ctok = (CommentToken) tok; // the current comment token
					if (onlyComments && leftComments != null)
						leftComments.add(ctok);
					appendCommentToken(out, ctok);
					break;

				default:
					Debug.ReportBug("Bad token type found.");
					break;
				}
			}
			
			if (keepLeftComments) { // we have comments to move to the end of the line
				for (CommentToken ctok : leftComments) {
					out.append(" (*");
					appendAndConvertCommentString(out, ctok.string, toU);
					out.append("*)");
				}
				final Token last = spec[line][spec[line].length-1]; 
				if (last.type == Token.COMMENT) {
					final CommentToken ctok = (CommentToken) last;
					// append skipped last comment token
					if (ctok.rsubtype == CommentToken.BEGIN_OVERRUN || ctok.rsubtype == CommentToken.LINE) {
						out.append(" ");
						appendCommentToken(out, ctok);
					}
				}
			}
			
			writer.putLine(out.toString());
		}
		writer.close();
	}
    
	private static void appendCommentToken(StringBuilder out, CommentToken ctok) {
		final String commentString = ctok.string;
		switch (ctok.rsubtype) {
		case CommentToken.NORMAL:
			out.append("(*");
			appendAndConvertCommentString(out, commentString, toU);
			out.append("*)");
			break;
		case CommentToken.LINE:
			out.append("\\*");
			appendAndConvertCommentString(out, commentString, toU);
			break;
		case CommentToken.BEGIN_OVERRUN:
			if (ctok.getWidth() > 0)
				out.append("(*");
				appendAndConvertCommentString(out, commentString, toU);
			break;
		case CommentToken.END_OVERRUN:
			appendAndConvertCommentString(out, commentString, toU);
			out.append("*)");
			break;
		case CommentToken.OVERRUN:
			appendAndConvertCommentString(out, commentString, toU);
			break;
		default:
			Debug.ReportBug("Bad CommentToken subtype found.");
		}
	}
	
	private static void appendAndConvertCommentString(StringBuilder out, String commentString, boolean toU) {
		if (toU)
			out.append(commentString);
		else {
			// We only support BMP chars, i.e. fit in a `char`, so we can work with chars rather than codepoints
			// Debug.Assert(isBMP(commentString), "Comment " + commentString + " contains non-BMP Unicode characters");
			char prev = 0; // the previous character
			for (int i = 0; i < commentString.length(); i++) { 
				final char c = commentString.charAt(i);
				if (Unicode.cu2a(c) != null /*!isASCII(c)*/) {
					String s = Unicode.cu2a(c);
					if (!Character.isWhitespace(prev))
						out.append(' '); // add whitespace before a unicode char
					out.append(s);
				} else if (!isASCII(c)) {
					Debug.Assert(false, "An unrecognized Unicode character " + c
							+ " was found in comment " + commentString);
				} else {
					if (Unicode.cu2a(prev) != null)
						out.append(' '); // add whitespace following a unicode char (or else /\x)
					out.append(c);
				}
				prev = c;
			}
		}
	}
	
	private static void appendSpaces(StringBuilder sb, int n) {
		for (int i = 0; i < n; i++)
			sb.append(' ');
	}
	
	private static boolean isInPcal(int line, int item) {
		return TokenizeSpec.hasPcal 
				&& line >= TokenizeSpec.pcalStart.line && item >= TokenizeSpec.pcalStart.item
				&& (line < TokenizeSpec.pcalEnd.line 
						|| (line == TokenizeSpec.pcalEnd.line && item < TokenizeSpec.pcalStart.item));
	}
    
	private static boolean isASCII(char c) {
		return c <= 0xff;
	}
	
	private static Token[][] filterOutComments(Token[][] spec) {
		List<Token[]> lines = new ArrayList<>();
		for (int i = 0; i < spec.length; i++) {
			List<Token> line = new ArrayList<>();
			for (int j = 0; j < spec[i].length; j++) {
				Token t = spec[i][j];
				if (t.type != Token.COMMENT)
					line.add(t);
			}
			lines.add(line.toArray(new Token[0]));
		}
		return lines.toArray(new Token[0][]);
	}
	
	// ----------- COMMAND LINE PARSING ---------------------------------------
	
  	private static boolean toU; // True for ASCII -> Unicode, false for Unicode -> ASCII
  	private static String inputFile = null ; // The name of the input file
  	private static String outputFile = null ; // The name of the output file
  
	public static void main(String[] args) {
		// ToolIO.out.println(version);
		getArguments(args); // Get the command-line arguments.

		final CharReader input = inputFile != null ? 
				new FileCharReader(inputFile) : new InputStreamCharReader(System.in);
		final OutputFileWriter output = outputFile != null 
				? new OutputFileWriter(outputFile) : new OutputFileWriter(System.out, "STDOUT");
				
		convert(toU, input, output);
	}
	
	private static void getArguments(String[] args) {
		 // Get the command-line arguments and set the appropriate static fields.
		
		if (args.length == 0)
			commandLineError("No arguments specified");
		
		boolean hasOp = false; // Whether or not -a2u or -u2a has been encountered.
		int argi = 0; // The index of the command line argument being processed.
		loop:
		while (argi < args.length) {
			// Process all the arguments, except for the last (unless it's a "-" argument).
			final String option = args[argi];
			switch(option) {
			case "-help":
				System.err.println(USAGE);
				System.exit(0);
				break;
			case "-debug":
				debug = true;
				break;
			case "-a2u":
				if (hasOp)
					commandLineError("Only one of -a2u or -u2a must be specified");
				hasOp = true;
				toU = true;
				break;
			case "-u2a":
				if (hasOp)
					commandLineError("Only one of -a2u or -u2a must be specified");
				hasOp = true;
				toU = false;
				break;
			default:
				if (option.startsWith("-"))
					commandLineError("Unsupported option " + option);
				break loop;
			}
			argi++;
		}
		if (!hasOp)
			commandLineError("One of -a2u or -u2a must be specified");

		// Input file
		if (argi >= args.length) {
			inputFile = null;
			return;
		}
		
		inputFile = args[argi];
		
		argi++;
		
		// Output file
		if (argi >= args.length) {
			outputFile = null;
			return;
		}
		
		outputFile = args[argi];
		// Report an error if inputFile = outFile.
		if (Objects.equals(Paths.get(inputFile).normalize().toAbsolutePath(),
				Paths.get(outputFile).normalize().toAbsolutePath()))
			commandLineError("Output file is the same as the tla input file."
					+ " This would overwrite your input file, so I won't do it");
	}

	private static void commandLineError(String msg) {
		ToolIO.out.println(APP + " command-line error: " + msg + ".");
		ToolIO.out.println(USAGE);
		throw new TLA2TexException(
				APP + " command-line error: " + msg + "." + "Use -help option for more information.");
	}
}

/*
Interesting test cases:
-------------------------

------------------------------- MODULE Bar -------------------------------
\* Comment replacement in A->U:

A == x /\ y /\ z /\ w
(*a1234ssasass*) /\ k
(*a12*)(*a*)(*c*)/\ a \* foo
(*a123*)         /\ k
(*a*)(*a*)       /\ a

B == x /\ y /\ z /\ w (* asasvjhsad
a1234ssasassas*) /\ k (* saiork
kinda*)          /\ t

\* "Accidental comment anchoring" in A->U:
Foo(a, b) == /\ a \/ b
          \* /\ a => b
             /\ b => a
=============================================================================



------------------------------- MODULE Bar -------------------------------
\* Comment replacement in U->A

A ≜ abcdefgd ∧ defjhfkjkh
(*a∧b∧c∧d∧e*)∧ k
=============================================================================

 */
