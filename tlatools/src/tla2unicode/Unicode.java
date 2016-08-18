package tla2unicode;

import java.io.IOException;
import java.io.Writer;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Converts between ASCII and Unicode represeantations of TLA+ symbols.
 * @author pron
 */
public final class Unicode {
	private Unicode() {}
	
	private static final Set<String> IMMEDIATE_REPLACE = new HashSet<String>(Arrays.asList(
			"\\/", "/\\", "[]", "<>", "<<", ">>", "|->", "->", "<-"
		));
	
	private static final String ASCII_GLYPHS = "=<>()+-\\/#.|~!$&*:";
	
	// Unicode/ASCII conversion table
	private static final String[][] table = { 
			// The first element is the Unicode character.
			// The second element is the canonical ASCII representation.
			// Subsequent elements are alternate ASCII representations.

			{ "\u225C", "==" },  // ≜ DELTA EQUAL TO 
			{ "\u2190", "<-" },  // ← LEFTWARDS ARROW
			{ "\u2192", "->" },  // → RIGHTWARDS ARROW
			{ "\u21A6", "|->" }, // ↦ RIGHTWARDS ARROW FROM BAR

			{ "\u27E8", "<<" },   // ⟨ MATHEMATICAL LEFT ANGLE BRACKET
			{ "\u27E9", ">>" },   // ⟩ MATHEMATICAL RIGHT ANGLE BRACKET
			{ "\u27E9_", ">>_" }, // ⟩_

			{ "\u2032", "'" },  // ′ PRIME
			{ "\u25FB", "[]" }, // ◻ White medium square / □ \u25A1 WHITE SQUARE / \u2610︎ ☐ BALLOT BOX 
			{ "\u2B26", "<>" }, // ⬦ WHITE MEDIUM DIAMOND / ♢ \u2662 WHITE DIAMOND SUIT
			{ "\u2933", "~>" },   // ⤳ WAVE ARROW POINTING DIRECTLY RIGHT
			{ "\u2945", "-+->" }, // ⥅ RIGHTWARDS ARROW WITH PLUS BELOW/ ⇾ \u21FE RIGHTWARDS OPEN-HEADED ARROW
			{ "\u2200\u2200", "\\AA" }, // ∀∀
			{ "\u2203\u2203", "\\EE" }, // ∃∃

			{ "\u2200", "\\A", "\\forall" }, // ∀ FOR ALL
			{ "\u2203", "\\E", "\\exists" }, // ∃ THERE EXISTS

			{ "\u00ac", "~", "\\lnot", "\\neg" }, // ¬ NOT SIGN
			{ "\u2227", "/\\", "\\land" },        // ∧ LOGICAL AND 
			{ "\u2228", "\\/", "\\lor" },         // ∨ LOGICAL OR
			{ "\u21D2", "=>" },                   // ⇒ RIGHTWARDS DOUBLE ARROW
			{ "\u2263", "<=>", "\\equiv" },       // ≣ STRICTLY EQUIVALENT TO / ⇔ \u21D4 LEFT RIGHT DOUBLE ARROW

			{ "\u2260", "#", "/=" }, // ≠ NOT EQUAL TO

			{ "\u2208", "\\in" },       // ∈ ELEMENT OF
			{ "\u2209", "\\notin" },    // ∉ NOT AN ELEMENT OF
			{ "\u2282", "\\subset" },   // ⊂ SUBSET OF
			{ "\u2286", "\\subseteq" }, // ⊆ SUBSET OF OR EQUAL TO
			{ "\u2283", "\\supset" },   // ⊃ SUPERSET OF
			{ "\u2287", "\\supseteq" }, // ⊇ SUPERSET OF OR EQUAL TO

			{ "\u2229", "\\cap", "\\intersect" }, // ∩ INTERSECTION
			{ "\u222A", "\\cup", "\\union" },     // ∪ UNION
			{ "\u228E", "\\uplus" },              // ⊎ MULTISET UNION

			{ "\u2264", "<=", "=<", "\\leq" }, // ≤ LESS-THAN OR EQUAL TO
			{ "\u2265", ">=", "\\geq" },       // ≥ GREATER-THAN OR EQUAL TO
			{ "\u226A", "\\ll" },              // ≪ MUCH LESS-THAN
			{ "\u226B", "\\gg" },              // ≫ MUCH GREATER-THAN

			{ "%", "%", "\\mod" }, 
			{ "\u00D7", "\\X", "\\times" }, // × MULTIPLICATION SIGN
			{ "\u00F7", "\\div" },          // ÷ DIVISION SIGN
			{ "\u22C5", "\\cdot" },         // ⋅ DOT OPERATOR

			{ "\u2295", "(+)", "\\oplus" },    // ⊕ CIRCLED PLUS
			{ "\u2296", "(-)", "\\ominus" },   // ⊖ CIRCLED MINUS
			{ "\u2297", "(X)", "\\otimes" }, // ⊗ CIRCLED TIMES
			{ "\u2298", "(/)", "\\oslash" },   // ⊘ CIRCLED DIVISION SLASH
			{ "\u2299", "(.)", "\\odot" },     // ⊙ CIRCLED DOT OPERATOR

			{ "\u25CB", "\\o", "\\circ" }, // ○ WHITE CIRCLE
			{ "\u25EF", "\\bigcirc" },     // ◯ LARGE CIRCLE 
			{ "\u2022", "\\bullet" },      // • BULLET 
			{ "\u2B51", "\\star" },        // ⭑ BLACK SMALL STAR / ★ \u2605 BLACK STAR / ☆ \u2606 WHITE STAR / ⭐︎ \u2B50 \uFE0E White medium star

			{ "\u227A", "\\prec" },   // ≺ PRECEDES
			{ "\u227C", "\\preceq" }, // ≼ PRECEDES OR EQUAL TO / ⪯ \u2AAF PRECEDES ABOVE SINGLE-LINE EQUALS SIGN
			{ "\u227B", "\\succ" },   // ≻ SUCCEEDS
			{ "\u227D", "\\succeq" }, // ≽ SUCCEEDS OR EQUAL TO / \u2AB0 ⪰ SUCCEEDS ABOVE SINGLE-LINE EQUALS SIGN

			{ "\u228F", "\\sqsubset" },   // ⊏ SQUARE IMAGE OF
			{ "\u2291", "\\sqsubseteq" }, // ⊑ SQUARE IMAGE OF OR EQUAL TO
			{ "\u2290", "\\sqsupset" },   // ⊐ SQUARE ORIGINAL OF
			{ "\u2292", "\\sqsupseteq" }, // ⊒ SQUARE ORIGINAL OF OR EQUAL TO

			{ "\u2293", "\\sqcap" }, // ⊓ SQUARE CAP
			{ "\u2294", "\\sqcup" }, // ⊔ SQUARE CUP

			{ "\u224D", "\\asymp" },  // ≍ EQUIVALENT TO
			{ "\u2240", "\\wr" },     // ≀ WREATH PRODUCT
			{ "\u2245", "\\cong" },   // ≅ APPROXIMATELY EQUAL TO
			{ "\u221D", "\\propto" }, // ∝ PROPORTIONAL TO
			{ "\u2248", "\\approx" }, // ≈ ALMOST EQUAL TO
			{ "\u2250", "\\doteq" },  // ≐ APPROACHES THE LIMIT
			{ "\u2243", "\\simeq" },  // ≃ ASYMPTOTICALLY EQUAL TO
			{ "\uFF5E", "\\sim" },    // ～ FULLWIDTH TILDE / ⩬ \u2A6C, SIMILAR MINUS SIMILAR / ⋍ \u22CD REVERSED TILDE EQUALS

			{ "\u22A2", "|-" }, // ⊢ RIGHT TACK
			{ "\u22A3", "-|" }, // ⊣ LEFT TACK 
			{ "\u22A8", "|=" }, // ⊨ TRUE
			{ "\u2AE4", "=|" }, // ⫤ VERTICAL BAR DOUBLE LEFT TURNSTILE

			{ "\u2016", "||" }, // ‖ DOUBLE VERTICAL LINE
			// { SUPERSCRIPT_PLUS, "^+" }, // ⁺ SUPERSCRIPT PLUS SIGN 
	};
	
	// Greek letters
	
	public static final char CAPITAL_GAMMA   = '\u0393'; // Γ GREEK CAPITAL LETTER GAMMA
	public static final char CAPITAL_DELTA   = '\u0394'; // Δ GREEK CAPITAL LETTER DELTA
	public static final char CAPITAL_THETA   = '\u0398'; // Θ GREEK CAPITAL LETTER THETA
	public static final char CAPITAL_LAMBDA  = '\u039B'; // Λ GREEK CAPITAL LETTER LAMDA
	public static final char CAPITAL_XI      = '\u039E'; // Ξ GREEK CAPITAL LETTER XI
	public static final char CAPITAL_PI      = '\u03A0'; // Π GREEK CAPITAL LETTER PI
	public static final char CAPITAL_SIGMA   = '\u03A3'; // Σ GREEK CAPITAL LETTER SIGMA
	public static final char CAPITAL_UPSILON = '\u03A5'; // Υ GREEK CAPITAL LETTER UPSILON
	public static final char CAPITAL_PHI     = '\u03A6'; // Φ GREEK CAPITAL LETTER PHI
	public static final char CAPITAL_PSI     = '\u03A8'; // Ψ GREEK CAPITAL LETTER PSI
	public static final char CAPITAL_OMEGA   = '\u03A9'; // Ω GREEK CAPITAL LETTER OMEGA
	
	public static final char SMALL_ALPHA   = '\u03B1'; // α GREEK SMALL LETTER ALPHA
	public static final char SMALL_BETA_   = '\u03B2'; // β GREEK SMALL LETTER BETA
	public static final char SMALL_GAMMA   = '\u03B3'; // γ GREEK SMALL LETTER GAMMA
	public static final char SMALL_DELTA   = '\u03B4'; // δ GREEK SMALL LETTER DELTA
	public static final char SMALL_EPSILON = '\u03B5'; // ε GREEK SMALL LETTER EPSILON
	public static final char SMALL_ZETA    = '\u03B6'; // ζ GREEK SMALL LETTER ZETA
	public static final char SMALL_ETA     = '\u03B7'; // η GREEK SMALL LETTER ETA
	public static final char SMALL_THETA   = '\u03B8'; // θ GREEK SMALL LETTER THETA
	public static final char SMALL_IOTA    = '\u03B9'; // ι GREEK SMALL LETTER IOTA
	public static final char SMALL_KAPPA   = '\u03BA'; // κ GREEK SMALL LETTER KAPPA
	public static final char SMALL_LAMBDA  = '\u03BB'; // λ GREEK SMALL LETTER LAMDA
	public static final char SMALL_MU      = '\u03BC'; // μ GREEK SMALL LETTER MU
	public static final char SMALL_NU      = '\u03BD'; // ν GREEK SMALL LETTER NU
	public static final char SMALL_XI      = '\u03BE'; // ξ GREEK SMALL LETTER XI
	public static final char SMALL_PI      = '\u03C0'; // π GREEK SMALL LETTER PI
	public static final char SMALL_RHO     = '\u03C1'; // ρ GREEK SMALL LETTER RHO
	public static final char SMALL_SIGMA   = '\u03C3'; // σ GREEK SMALL LETTER SIGMA
	public static final char SMALL_TAU     = '\u03C4'; // τ GREEK SMALL LETTER TAU
	public static final char SMALL_UPSILON = '\u03C5'; // υ GREEK SMALL LETTER UPSILON
	public static final char SMALL_PHI     = '\u03C6'; // φ GREEK SMALL LETTER PHI
	public static final char SMALL_PHI_1   = '\u0278'; // ɸ LATIN SMALL LETTER PHI
	public static final char SMALL_CHI     = '\u03C7'; // χ GREEK SMALL LETTER CHI
	public static final char SMALL_PSI     = '\u03C8'; // ψ GREEK SMALL LETTER PSI
	public static final char SMALL_OMEGA   = '\u03C9'; // ω GREEK SMALL LETTER OMEGA

	// Subscripts (◻[Next]ᵥₐᵣₛ)
	
	public static final char subscriptDigit(int num) { // ₀₁₂₃₄₅₆₇₈₉
		assert num >= 0 && num <= 9;
		return (char)(0x2080 + num);
	}

	public static final char SUBSCRIPT_a = '\u2090'; // ₐ LATIN SUBSCRIPT SMALL LETTER A
	public static final char SUBSCRIPT_e = '\u2091'; // ₑ LATIN SUBSCRIPT SMALL LETTER E
	public static final char SUBSCRIPT_h = '\u2095'; // ₕ LATIN SUBSCRIPT SMALL LETTER H
	public static final char SUBSCRIPT_i = '\u1D62'; // ᵢ LATIN SUBSCRIPT SMALL LETTER I
	public static final char SUBSCRIPT_j = '\u2C7C'; // ⱼ LATIN SUBSCRIPT SMALL LETTER J
	public static final char SUBSCRIPT_k = '\u2096'; // ₖ LATIN SUBSCRIPT SMALL LETTER K
	public static final char SUBSCRIPT_l = '\u2097'; // ₗ LATIN SUBSCRIPT SMALL LETTER L
	public static final char SUBSCRIPT_m = '\u2098'; // ₘ LATIN SUBSCRIPT SMALL LETTER M
	public static final char SUBSCRIPT_n = '\u2099'; // ₙ LATIN SUBSCRIPT SMALL LETTER N
	public static final char SUBSCRIPT_o = '\u2092'; // ₒ LATIN SUBSCRIPT SMALL LETTER O
	public static final char SUBSCRIPT_p = '\u209A'; // ₚ LATIN SUBSCRIPT SMALL LETTER P
	public static final char SUBSCRIPT_r = '\u1D63'; // ᵣ LATIN SUBSCRIPT SMALL LETTER R
	public static final char SUBSCRIPT_s = '\u209B'; // ₛ LATIN SUBSCRIPT SMALL LETTER S
	public static final char SUBSCRIPT_t = '\u209C'; // ₜ LATIN SUBSCRIPT SMALL LETTER T
	public static final char SUBSCRIPT_u = '\u1D64'; // ᵤ LATIN SUBSCRIPT SMALL LETTER U
	public static final char SUBSCRIPT_v = '\u1D65'; // ᵥ LATIN SUBSCRIPT SMALL LETTER V
	public static final char SUBSCRIPT_x = '\u2093'; // ₓ LATIN SUBSCRIPT SMALL LETTER X
	public static final char SUBSCRIPT_SMALL_BETA  = '\u1D66'; // ᵦ GREEK SUBSCRIPT SMALL LETTER BETA
	public static final char SUBSCRIPT_SMALL_GAMMA = '\u1D67'; // ᵧ GREEK SUBSCRIPT SMALL LETTER GAMMA
	public static final char SUBSCRIPT_SMALL_PHI   = '\u1D69'; // ᵩ GREEK SUBSCRIPT SMALL LETTER PHI
	public static final char SUBSCRIPT_SMALL_CHI   = '\u1D6A'; // ᵪ GREEK SUBSCRIPT SMALL LETTER CHI

	public static final char SUBSCRIPT_PLUS = '\u208A'; // ₊ SUBSCRIPT PLUS SIGN

	// Superscripts
	
	private static final char[] SUPERSCRIPT_DIGIT = { 
			'\u2070', '\u00B9', '\u00B2', '\u00B3', '\u2074', '\u2075', '\u2076', '\u2077', '\u2078', '\u2079'
		};

	public static final char superscriptDigit(int num) { // ⁰¹²³⁴⁵⁶⁷⁸⁹
		assert num >= 0 && num <= 9;
		return SUPERSCRIPT_DIGIT[num];
	}	
	
	public static final char SUPERSCRIPT_PLUS = '\u207A'; // ⁺ SUPERSCRIPT PLUS SIGN 
	public static final char SUBSCRIPT_ASTERISK = '\u204E'; // ⁎ LOW ASTERISK
		
//	Box drawing:

	public static final char HORIZONTAL      = '\u2500'; // ─ BOX DRAWINGS LIGHT HORIZONTAL         /  ━ \u2501 HEAVY
	public static final char BMODULE_BEGIN   = '\u250C'; // ┌ BOX DRAWINGS LIGHT DOWN AND RIGHT     / ┏ \u250F HEAVY
	public static final char BMODULE_END     = '\u2510'; // ┐ BOX DRAWINGS LIGHT DOWN AND LEFT      /  ┓ \u2513 HEAVY
	public static final char SEPARATOR_BEGIN = '\u251C'; // ├ BOX DRAWINGS LIGHT VERTICAL AND RIGHT / ┣ \u2523 HEAVY
	public static final char SEPARATOR_END   = '\u2524'; // ┤ BOX DRAWINGS LIGHT VERTICAL AND LEFT  / ┫ \u252B HEAVY
	public static final char EMODULE_BEGIN   = '\u2514'; // └ BOX DRAWINGS LIGHT UP AND RIGHT       / ┗ \u2517 HEAVY
	public static final char EMODULE_END     = '\u2518'; // ┘ BOX DRAWINGS LIGHT UP AND LEFT        / ┛ \u251B HEAVY
	
	///////////////////////////////////////////////////////////////////////////////////
	
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
	 *         or if {@code a} is not the canonical represeantation.
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
	
	public static void main(String[] args) {
		for (String a : new String[] {"<<-3>>", "<-3", "===", "==1"}) {
			System.out.println(a);
			System.out.println(convertToUnicode(a));
			System.out.println(convertToASCII(convertToUnicode(a)));
			System.out.println("-----");
		}
	}
}
