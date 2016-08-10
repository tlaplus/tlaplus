// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS WriteTLAFile                                                       *
*                                                                          *
* Contains the method Write for writing out a tokenized spec as a TLA      *
* file, deleting the "`^ ... ^'" parts of comments, and replacing "`~",    *
* "~'", "`.", and ".'" by spaces.                                          *
***************************************************************************/
package unicasc;

import tla2tex.BuiltInSymbols;
import tla2tex.CommentToken;
import tla2tex.Debug;
import tla2tex.OutputFileWriter;
import tla2tex.Symbol;
import tla2tex.Token;
import tla2tex.TokenizeSpec;

public class A2U {
	public static void a2u(Token[][] spec, OutputFileWriter writer) {
		Write(spec, writer, true);
	}
	
	public static void u2a(Token[][] spec, OutputFileWriter writer) {
		Write(spec, writer, false);
	}
	
	public static void Write(Token[][] spec, OutputFileWriter writer, boolean toU) {
		for (int line = 0; line < spec.length; line++) {
			final StringBuilder out = new StringBuilder();
			for (int item = 0; item < spec[line].length; item++) {
				final Token tok = spec[line][item];
				// out.append("$" + tok + "$");
				
				int space = -1; // how much space to leave before the token
				if (tok.aboveAlign.line != -1) {
					// if aligned to a token above -- keep alignment
					Token align = tok.aboveAlign.toToken(spec);
					if (align.column == tok.column) {
						final int column = out.length();
						space = align.outcolumn - column;
						
						if (space < 0/* && !isFirstNonCommentToken(spec, line, item)*/)
							out.append("$" + space + "$");
					}
				} 
					
				if (space < 0) // keep original spacing
					space = tok.column - (item > 0 ? spec[line][item - 1].column + spec[line][item - 1].getWidth() : 0);
				
				Debug.Assert(space >= 0, tok + (item > 0 ? " :: " + spec[line][item - 1] : ""));
				appendSpaces(out, space);

//				System.out.println(":1: " + tok.column + " " + out.length());			
//				System.out.println(":2: " + tok.column + " " + out.length());
//				System.out.println(":3: " + tok);
				
				tok.outcolumn = out.length();

				switch (tok.type) {
				case Token.BUILTIN: {
					final Symbol sym = BuiltInSymbols.GetBuiltInSymbol(tok.string, inPcal(line, item));
					Debug.Assert(sym != null, "Symbol for builtin tolen not found: " + tok);
					
					if (Symbol.isUnicode(tok.string) != toU && sym.alternate != null && Symbol.isUnicode(sym.alternate)) {
						out.append(sym.alternate);
						tok.outstring = sym.alternate;
					} else
						out.append(tok.string);
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
					/*************************************************************
					 * Set ctok to the current comment token we are processing.	
					 *************************************************************/
					CommentToken ctok = (CommentToken) tok;

					String commentString = ctok.string;

					if (ctok != null) {
						switch (ctok.rsubtype) {
						case CommentToken.NORMAL:
							out.append("(*" + commentString + "*)");
							break;
						case CommentToken.LINE:
							out.append("\\*" + commentString);
							break;
						case CommentToken.BEGIN_OVERRUN:
							if (ctok.getWidth() > 0)
								out.append("(*" + commentString);
							break;
						case CommentToken.END_OVERRUN:
							out.append(commentString + "*)");
							break;
						case CommentToken.OVERRUN:
							out.append(commentString);
							break;
						default:
							Debug.ReportBug("Bad CommentToken subtype found.");
						}
					}
					break;

				default:
					Debug.ReportBug("Bad token type found.");
					break;
				}
			}
			writer.putLine(out.toString());
		}
		writer.close();
	}

	private static boolean isFirstNonCommentToken(Token[][] spec, int line, int item) {
		for (int i=0; i<item; i++) {
			if (spec[line][i].type != Token.COMMENT)
				return false;
		}
		return true;
	}
	
	// A string of n spaces.
	private static void appendSpaces(StringBuilder sb, int n) {
		for (int i = 0; i < n; i++)
			sb.append(' ');
	}
	
	private static boolean inPcal(int line, int item) {
		return TokenizeSpec.hasPcal 
				&& line >= TokenizeSpec.pcalStart.line && item >= TokenizeSpec.pcalStart.item
				&& (line < TokenizeSpec.pcalEnd.line || (line == TokenizeSpec.pcalEnd.line && item < TokenizeSpec.pcalStart.item));
	}
}