package tla2unicode;

import java.io.IOException;
import java.io.Writer;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import static tla2unicode.UnicodeConstants.*;

/**
 * Converts between ASCII and Unicode represeantations of TLA+ symbols.
 * @author pron
 */
public final class Unicode {
	// See Isabelle/etc/symbols https://github.com/seL4/isabelle/blob/master/etc/symbols
	
	private Unicode() {}
	
	// The following two constants are used in online Unicode replacement
	private static final String ASCII_GLYPHS = "=<>[]()+-\\/#.|~!$&*:'^";
	public static final Set<String> IMMEDIATE_REPLACE = new HashSet<String>(Arrays.asList(
			"\\/", "/\\", "[]", "<>", "<<", ">>", "|->", "->", "<-"
		));

	// Unicode/ASCII conversion table
	private static final String[][] table = { 
			// The first element is the Unicode character.
			// The second element is the canonical ASCII representation.
			// Subsequent elements are alternate ASCII representations.

			{ "" + DELTA_EQUAL_TO,   "==" },  // ≜ DELTA EQUAL TO 
			{ "" + LEFTWARDS_ARROW,  "<-" },  // ← LEFTWARDS ARROW
			{ "" + RIGHTWARDS_ARROW, "->" },  // → RIGHTWARDS ARROW
			{ "" + MAPS_TO,          "|->" }, // ↦ RIGHTWARDS ARROW FROM BAR

			{ "" + LEFT_ANGLE_BRACKET,        "<<" },  // ⟨ MATHEMATICAL LEFT ANGLE BRACKET
			{ "" + RIGHT_ANGLE_BRACKET,       ">>" },  // ⟩ MATHEMATICAL RIGHT ANGLE BRACKET
			{ "" + RIGHT_ANGLE_BRACKET + "_", ">>_" }, // ⟩_

			{ "" + PRIME, "'" },  // ′ PRIME
			{ "" + WHITE_SQUARE, "[]" }, // □ \u25A1 WHITE SQUARE / ◻ \u25FB White medium square / \u2610︎ ☐ BALLOT BOX  / \u2B1C ⬜ White large square
			{ "" + WHITE_DIAMOND, "<>" }, // ◇ \u25C7 WHITE DIAMOND/ ⬦ \u2B26 WHITE MEDIUM DIAMOND / ♢ \u2662 WHITE DIAMOND SUIT 
			{ "" + RIGHTWARDS_WAVE_ARROW, "~>" },   // ↝ \u219D RIGHTWARDS WAVE ARROW / ⤳ \u2933 WAVE ARROW POINTING DIRECTLY RIGHT
			{ "" + RIGHTWARDS_ARROW_PLUS, "-+->" }, // ⥅ RIGHTWARDS ARROW WITH PLUS BELOW/ ⇾ \u21FE RIGHTWARDS OPEN-HEADED ARROW
			{ "" + FORALL + FORALL, "\\AA" }, // ∀∀
			{ "" + EXISTS + EXISTS, "\\EE" }, // ∃∃

			{ "" + FORALL, "\\A", "\\forall" }, // ∀ FOR ALL
			{ "" + EXISTS, "\\E", "\\exists" }, // ∃ THERE EXISTS

			{ "" + NOT,     "~", "\\lnot", "\\neg" }, // ¬ NOT SIGN
			{ "" + AND,     "/\\", "\\land" },        // ∧ LOGICAL AND 
			{ "" + OR,      "\\/", "\\lor" },         // ∨ LOGICAL OR
			{ "" + IMPLIES, "=>" },                   // ⇒ RIGHTWARDS DOUBLE ARROW
			{ "" + IDENT,   "<=>", "\\equiv" },       // ≡ IDENTICAL TO / ⇔ \u21D4 LEFT RIGHT DOUBLE ARROW 

			{ "" + NEQUAL, "#", "/=" }, // ≠ NOT EQUAL TO

			{ "" + ELEM,     "\\in" },       // ∈ ELEMENT OF
			{ "" + NELEM,    "\\notin" },    // ∉ NOT AN ELEMENT OF
			{ "" + SUBSET,   "\\subset" },   // ⊂ SUBSET OF
			{ "" + SUBSETEQ, "\\subseteq" }, // ⊆ SUBSET OF OR EQUAL TO
			{ "" + SUPSET,   "\\supset" },   // ⊃ SUPERSET OF
			{ "" + SUPSETEQ, "\\supseteq" }, // ⊇ SUPERSET OF OR EQUAL TO

			{ "" + XION , "\\cap", "\\intersect" }, // ∩ INTERSECTION
			{ "" + UNION, "\\cup", "\\union" },     // ∪ UNION
			{ "" + UPLUS, "\\uplus" },              // ⊎ MULTISET UNION

			{ "" + LEQ,  "<=", "=<", "\\leq" }, // ≤ LESS-THAN OR EQUAL TO
			{ "" + GEQ,  ">=", "\\geq" },       // ≥ GREATER-THAN OR EQUAL TO
			{ "" + LTLT, "\\ll" },              // ≪ MUCH LESS-THAN
			{ "" + GTGT, "\\gg" },              // ≫ MUCH GREATER-THAN

			{ "%", "%", "\\mod" }, 
			{ "" + MULT, "\\X", "\\times" }, // × MULTIPLICATION SIGN
			{ "" + DIV,  "\\div" },          // ÷ DIVISION SIGN
			{ "" + DOT,  "\\cdot" },         // ⋅ DOT OPERATOR

			{ "" + OPLUS,  "(+)", "\\oplus" },  // ⊕ CIRCLED PLUS
			{ "" + OMINUS, "(-)", "\\ominus" }, // ⊖ CIRCLED MINUS
			{ "" + OTIMES, "(X)", "\\otimes" }, // ⊗ CIRCLED TIMES
			{ "" + OSLASH, "(/)", "\\oslash" }, // ⊘ CIRCLED DIVISION SLASH
			{ "" + ODOT,   "(.)", "\\odot" },   // ⊙ CIRCLED DOT OPERATOR

			{ "" + RING,         "\\o", "\\circ" }, // ∘ \u2218 RING OPERATOR / ○ \u25CB WHITE CIRCLE
			{ "" + LARGE_CIRCLE, "\\bigcirc" },     // ◯ LARGE CIRCLE 
			{ "" + BULLET,       "\\bullet" },      // • BULLET 
			{ "" + STAR,         "\\star" },        // ⋆ \u22c6 STAR OPERATOR / ⭑ \u2B51 BLACK SMALL STAR / ★ \u2605 BLACK STAR / ☆ \u2606 WHITE STAR / ⭐︎ \u2B50 \uFE0E White medium star
			
			{ "" + PREC,   "\\prec" },   // ≺ PRECEDES
			{ "" + PRECEQ, "\\preceq" }, // ≼ PRECEDES OR EQUAL TO / ⪯ \u2AAF PRECEDES ABOVE SINGLE-LINE EQUALS SIGN
			{ "" + SUCC,   "\\succ" },   // ≻ SUCCEEDS
			{ "" + SUCCEQ, "\\succeq" }, // ≽ SUCCEEDS OR EQUAL TO / \u2AB0 ⪰ SUCCEEDS ABOVE SINGLE-LINE EQUALS SIGN

			{ "" + SQSUB,   "\\sqsubset" },   // ⊏ SQUARE IMAGE OF
			{ "" + SQSUBEQ, "\\sqsubseteq" }, // ⊑ SQUARE IMAGE OF OR EQUAL TO
			{ "" + SQSUP,   "\\sqsupset" },   // ⊐ SQUARE ORIGINAL OF
			{ "" + SQSUPEQ, "\\sqsupseteq" }, // ⊒ SQUARE ORIGINAL OF OR EQUAL TO

			{ "" + SQCAP, "\\sqcap" }, // ⊓ SQUARE CAP
			{ "" + SQCUP, "\\sqcup" }, // ⊔ SQUARE CUP

			{ "" + EQUIVALENT_TO, "\\asymp" },  // ≍ EQUIVALENT TO
			{ "" + WREATH,   "\\wr" },     // ≀ WREATH PRODUCT
			{ "" + APPROXEQ, "\\cong" },   // ≅ APPROXIMATELY EQUAL TO
			{ "" + PROPTO,   "\\propto" }, // ∝ PROPORTIONAL TO
			{ "" + APPROX,   "\\approx" }, // ≈ ALMOST EQUAL TO
			{ "" + DOTEQ,    "\\doteq" },  // ≐ APPROACHES THE LIMIT
			{ "" + SIMEQ,    "\\simeq" },  // ≃ ASYMPTOTICALLY EQUAL TO
			{ "" + FULLWIDTH_TILDE, "\\sim" },    // ～ FULLWIDTH TILDE / ⩬ \u2A6C, SIMILAR MINUS SIMILAR

			{ "" + TURNSTILE,             "|-" }, // ⊢ RIGHT TACK
			{ "" + LEFT_TURNSTILE,        "-|" }, // ⊣ LEFT TACK 
			{ "" + DOUBLE_TURNSTILE,      "|=" }, // ⊨ TRUE
			{ "" + DOUBLE_LEFT_TURNSTILE, "=|" }, // ⫤ VERTICAL BAR DOUBLE LEFT TURNSTILE

			{ "" + PAR, "||" }, // ‖ DOUBLE VERTICAL LINE
			// { "" + SUPERSCRIPT_PLUS, "^+" }, // ⁺ SUPERSCRIPT PLUS SIGN 
	};

	////////////////////////////////////////////////////////////////////
	
	private static final Map<String, String> u2a = new HashMap<>();
	private static final Map<String, String> a2u = new HashMap<>();
	private static final Map<Character, String> cu2a = new HashMap<>();
	
	static {
		// initialize maps
		for (String[] row : table) {
			final String u = row[0]; // unicode
			u2a.put(u, row[1]);
			if(u.length() == 1)
				cu2a.put(u.charAt(0), row[1]);
			for (int i = 1; i < row.length; i++)
				a2u.put(row[i], u);
		}
	}


	/**
	 * The canonical ASCII representation of a Unicode string
	 * 
	 * @param u the Unicode string
	 * @return the canonical ASCII string or {@code null} if no alternate
	 *         representation
	 */
	public static String u2a(String u) {
		return u2a.get(u);
	}
	
	/**
	 * The canonical ASCII representation of a Unicode character
	 * 
	 * @param u the Unicode string
	 * @return the canonical ASCII string or {@code null} if no alternate
	 *         representation
	 */
	public static String cu2a(char u) {
		return cu2a.get(u);
	}

	/**
	 * The Unicode representation of an ASCII string
	 * 
	 * @param a
	 *            the ASCII string
	 * @return the Unicode string or {@code null} if no alternate representation
	 */
	public static String a2u(String a) {
		return a2u.get(a);
	}

	/**
	 * The Unicode representation of a canonical ASCII string
	 * 
	 * @param a the ASCII string
	 * @return the Unicode string or {@code null} if no alternate representation
	 *         or if {@code a} is not the canonical representation.
	 */
	public static String a2uc(String a) {
		String res = a2u.get(a);
		if (res != null && !u2a.get(res).equals(a))
			res = null;
		return res;
	}
	
	/**
	 * A convenience method that returns the Unicode representation of a symbol (whether ASCII or Unicode)
	 * @param s the symbol (ASCII or Unicode)
	 * @return the possibly converted symbol
	 */
	public static String sym2u(String s) {
		String res;
		return (res = a2u(s)) != null ? res : s;
	}
	
	/**
	 * A convenience method that returns the ASCII representation of a symbol (whether Unicode or ASCII)
	 * @param s the symbol (Unicode or ASCII)
	 * @return the possibly converted symbol
	 */
	public static String sym2a(String s) {
		String res;
		return (res = u2a(s)) != null ? res : s;
	}
	
	/**
	 * Converts all relevant ASCII symbols in the given string to their Unicode representation. 
	 * @param in a string
	 * @return a string with ASCII symbols replaced
	 */
	public static String convertToUnicode(String in) {
		final StringBuilder out = new StringBuilder();
		final OnlineFilter r = new OnlineFilter() {
			@Override
			protected void putChar(char c) {
				out.append(c);
			}
			
			@Override
			protected void putString(CharSequence s) {
				out.append(s);
			}
		};

		for (int i = 0; i < in.length(); i++) {
			char c = in.charAt(i);
			r.addChar(c);
		}
		r.flush();
		return out.toString();
	}
	
	/**
	 * Converts all Unicode symbols in the given string to their ASCII representation. 
	 * @param in a string
	 * @return a string with Unicode symbols replaced
	 */
	public static String convertToASCII(String in) {
		final StringBuilder out = new StringBuilder();
		for (int i = 0; i < in.length(); i++) {
			char c = in.charAt(i);
			String u = cu2a(c);
			if (u != null)
				out.append(u);
			else
				out.append(c);
		}
		return out.toString();
	}
	
	public static String convert(boolean toU, String in) {
		return toU ? convertToUnicode(in) : convertToASCII(in);
	}
	
	public static String toSuperscript(int num) {
		String decimal = Integer.toString(num);
		StringBuilder sb = new StringBuilder(decimal.length());
		for (int i = 0; i < decimal.length(); i++)
			sb.append(superscriptDigit(decimal.charAt(i) - '\0'));
		return sb.toString();
	}
	
	public static String toSubrscript(int num) {
		String decimal = Integer.toString(num);
		StringBuilder sb = new StringBuilder(decimal.length());
		for (int i = 0; i < decimal.length(); i++)
			sb.append(subscriptDigit(decimal.charAt(i) - '\0'));
		return sb.toString();
	}
	
	/**
	 * Online replacement of ASCII -> Unicode as you type
	 */
	public static abstract class OnlineReplacer {
		protected StringBuilder token; // The current symbol token. Starts with '\' or contains only Unicode.ASCII_GLYPHS 
		private int startOffset; // the token's starting offset in the document
		private int nextOffset; // the position following the end of token (used in the state machine)

		public OnlineReplacer() {
			reset();
		}
		
		public final int getNextOffset() {
			return nextOffset;
		}
		
		// resets the token
		public final void reset() {
			// System.out.println("RESET");
			if (token == null || token.length() > 0)
				token = new StringBuilder();
			nextOffset = -1;
			startOffset = -1;
		}
		
		public final void backspace() {
			// System.out.println("backspace  start: " + startOffset + " next: " + nextOffset + " token: \"" + token + "\"");
			token.delete(token.length() - 1, token.length());
			nextOffset--;
		}
		
		public final void addChar(int offset, char c) {
			// This is the core of the state machine adding characters to token
			// and sending tokens for replacement.
			assert nextOffset < 0 || offset == nextOffset;
			
			// System.out.println("addChar  start: " + startOffset + " next: " + nextOffset + " token: \"" + token + "\"");
			
			if (token.length() > 0 && token.charAt(0) == '\\') {
				if (token.length() == 1 && c == '/') { // Special case: \/
					appendToToken(offset, c);
					replace();
				} else if (isBackslashOperatorChar(c)) {
					appendToToken(offset, c);
				} else {
					replace();
					addChar(offset, c);
				}
			} else if (Unicode.ASCII_GLYPHS.indexOf(c) >= 0
						|| (c == 'X' && token.length() == 1 && token.charAt(0) == '(')) { // Special case: (X)
				appendToToken(offset, c);
				if(IMMEDIATE_REPLACE.contains(token.toString()))
					replace();
			} else {
				replace();
				putChar(c);
			}
		}
		
		private void appendToToken(int offset, char c) {
			if (nextOffset < 0) {
				nextOffset = offset;
				startOffset = offset;
			}
			token.append(c);
			nextOffset++;
			// System.out.println("APPEND: " + token);
		}
		
		// Whether this char can be a part of a backslash operator
		private static boolean isBackslashOperatorChar(char c) {
			return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
		}
		
		public final void replace() {
			if (token.length() == 0)
				return;
			final String u = Unicode.a2u(token.toString());
			if (u != null) {
				// System.out.println("REPLACE " + token);
				replace(startOffset, token.length(), u);
			} else
				putString(token);
			reset();
		}
		
		protected abstract void replace(int start, int length, String u);
		
		protected void putString(CharSequence s) {
			for (int i = 0; i < s.length(); i++)
				putChar(s.charAt(i));
		}
		
		protected void putChar(char c) {
		}
	}
	
	/**
	 * Online Unicode filter with a simpler API than OnlineReplacer
	 * for simple, non-navigable streams.
	 */
	static abstract class OnlineFilter extends OnlineReplacer {
		public final void addChar(char c) {
			addChar(-1, c);
		}
		
		protected final void replace(int start, int length, String u) {
			putString(u);
		}
		
		public final void flush() {
			replace();
		}
		
		protected abstract void putChar(char c);
	}
	
	/**
	 * A Writer that replaces TLA ASCII symbols with their Unicode
	 * representation when relevant.
	 */
	public static final class TLAUnicodeWriter extends Writer {
		private final Writer out;
		private final OnlineFilter filter = new OnlineFilter() {
			@Override
			protected void putChar(char c) {
				try {
					out.append(c);
				} catch (IOException e) {
					throw new RuntimeException(e);
				}
			}

			@Override
			protected void putString(CharSequence s) {
				try {
					out.append(s);
				} catch (IOException e) {
					throw new RuntimeException(e);
				}
			}
		};
		
		public TLAUnicodeWriter(Writer out) {
			this.out = out;
		}

		@Override
		public void write(char[] cbuf, int off, int len) throws IOException {
			for (int i = 0; i < len; i++)
				write(cbuf[off + i]);
		}

		@Override
		public Writer append(CharSequence s) throws IOException {
			for (int i = 0; i < s.length(); i++)
				write(s.charAt(i));
			return this;
		}

		@Override
		public void write(int c) throws IOException {
			try {
				filter.addChar((char) c); 
			} catch (RuntimeException e) {
				if (e.getCause() instanceof IOException)
					throw (IOException) e.getCause();
				throw e;
			}
		}

		@Override
		public void flush() throws IOException {
			filter.flush();
			out.flush();
		}

		@Override
		public void close() throws IOException {
			filter.flush();
			out.close();
		}
	}
	
	/**
	 * Whether or not a string contains only BMP characters (TLA+ only supports those).
	 */
	public static boolean isBMP(String str) {
		return str.length() == str.codePointCount(0, str.length());
	}
	
//	public static void main(String[] args) {
//		for (String a : new String[] {"<<-3>>", "<-3", "===", "==1"}) {
//			System.out.println(a);
//			System.out.println(convertToUnicode(a));
//			System.out.println(convertToASCII(convertToUnicode(a)));
//			System.out.println("-----");
//		}
//	}
}
