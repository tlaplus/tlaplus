package unicasc;

import java.util.HashMap;
import java.util.Map;

/**
 * Converts between ASCII and Unicode represeantations of TLA+ symbols.
 * @author pron
 */
public final class Unicode {
	private Unicode() {}
	
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
			{ "\u2297", "(\\X)", "\\otimes" }, // ⊗ CIRCLED TIMES
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

//	/**
//	 * Convert to Unicode representation
//	 * 
//	 * @param a the ASCII string
//	 * @return the Unicode string or {@code a} if no alternate representation
//	 */
//	public static String toU(String a) {
//		return convert(a, true);
////		String u;
////		return ((u = a2u(a)) != null ? u : a);
//	}
//
//	/**
//	 * Convert to ASCII representation of a string
//	 * 
//	 * @param u the Unicode string
//	 * @return the canonical ASCII string or {@code a} if no alternate
//	 *         representation
//	 */
//	public static String toA(String u) {
//		return convert(u, false);
////		String a;
////		return ((a = u2a(u)) != null ? a : u);
//	}
//	
	private static final String ASCII_GLYPHS = "=<>()+-\\/#.|~";
	
	// <<-3>>
	// <-3
	
//	private static String convert(String in, boolean toU) {
//		StringBuilder out = new StringBuilder();
//		StringBuilder token = new StringBuilder();
//		for (int i = 0; i < in.length();) {
//			char c = in.charAt(i);
//			
//			if (c == '\\') {
//				if --- comment, \/, /\
//				convertToken(out, token, toU);
//				for (; i < in.length() && Character.isLetter(in.charAt(i)); i++)
//					token.append(c);
//				convertToken(out, token, toU);
//				continue;
//			}
//						
//			if (i < in.length() - 1) {
//				final char c1 = in.charAt(i + 1);
//				if ((c == '<' && (in.charAt(i + 1) == '<' || in.charAt(i + 1) == '>'))
//							|| (c == '[' && in.charAt(i + 1) == ']')) {
//					convertToken(out, token, toU);
//					token.append(c).append(c1); 
//					convertToken(out, token, toU);
//					i += 2;
//					continue;
//				}
//			}
//			
//			if (ASCII_GLYPHS.indexOf(c) >= 0) {
//				token.append(c);
//				i++;
//				continue;
//			}
//			
//			if (true /*Character.isWhitespace(c) || Character.isLetterOrDigit(c) || c == '_'*/) {
//				convertToken(out, token, toU);
//				out.append(c);
//				i++;
//				continue;
//			}
//		}
//		return out.toString();
//	}
	
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
	
	private static void convertToken(StringBuilder out, StringBuilder token, boolean toU) {
		if (token.length() > 0) {
			String res = toU ? a2u(token.toString()) : u2a(token.toString());
			out.append(res != null ? res : token);
		}
		token.setLength(0);
	}
	
	/**
	 * Whether or not a string contains only BMP characters (TLA+ only supports those).
	 */
	public static boolean isBMP(String str) {
		return str.length() == str.codePointCount(0, str.length());
	}
}
