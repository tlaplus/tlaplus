package unicasc;

import java.util.HashMap;
import java.util.Map;

/**
 * Converts between ASCII and Unicode represeantations of TLA+ symbols.
 * @author pron
 */
public final class Unicode {
	private Unicode() {}
	
	private static final Map<String, String> u2a = new HashMap<>();
	private static final Map<String, String> a2u = new HashMap<>();
	private static final Map<Character, String> cu2a = new HashMap<>();

	private static final String[][] table = { 
			{ "\u225C", "==" },  // ≜ DELTA EQUAL TO 
			{ "\u2190", "<-" },  // ← LEFTWARDS ARROW
			{ "\u2192", "->" },  // → RIGHTWARDS ARROW
			{ "\u21A6", "|->" }, // ↦ RIGHTWARDS ARROW FROM BAR

			{ "\u27E8", "<<" },   // ⟨ MATHEMATICAL LEFT ANGLE BRACKET
			{ "\u27E9", ">>" },   // ⟩ MATHEMATICAL RIGHT ANGLE BRACKET
			{ "\u27E9_", ">>_" }, // ⟩_

			{ "\u2200\u2200", "\\AA" }, // ∀∀
			{ "\u2203\u2203", "\\EE" }, // ∃∃
			{ "\u25FB", "[]" }, // ◻ White medium square / □ \u25A1 WHITE SQUARE / \u2610︎ ☐ BALLOT BOX 
			{ "\u2B26", "<>" }, // ⬦ WHITE MEDIUM DIAMOND / ♢ \u2662 WHITE DIAMOND SUIT
			{ "\u2032", "'" },  // ′ PRIME
			{ "\u2933", "~>" },   // ⤳ WAVE ARROW POINTING DIRECTLY RIGHT
			{ "\u2945", "-+->" }, // ⥅ RIGHTWARDS ARROW WITH PLUS BELOW/ ⇾ \u21FE RIGHTWARDS OPEN-HEADED ARROW

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

			// { "%", "%", "\\mod" }, 
			{ "\u00D7", "\\X", "\\times" }, // × MULTIPLICATION SIGN
			{ "\u00F7", "\\div" },          // ÷ DIVISION SIGN
			{ "\u22C5", "\\cdot" },         // ⋅ DOT OPERATOR

			{ "\u2295", "(+)", "\\oplus" },    // ⊕ CIRCLED PLUS
			{ "\u2296", "(-)", "\\ominus" },   // ⊖ CIRCLED MINUS
			{ "\u2297", "(\\X)", "\\otimes" }, // ⊗ CIRCLED TIMES
			{ "\u2298", "(/)", "\\oslash" },   // ⊘ CIRCLED DIVISION SLASH
			{ "\u2299", "(.)", "\\odot" },     // ⊙ CIRCLED DOT OPERATOR

			{ "\u25CB", "\\o", "\\circ" }, // ○ WHITE CIRCL
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
			// { "\u207A", "^+" }, // ⁺ SUPERSCRIPT PLUS SIGN 
	};
	
//	Box drawing:

	public static final char HORIZONTAL      = '\u2500'; // ─ BOX DRAWINGS LIGHT HORIZONTAL         /  ━ \u2501 HEAVY
	public static final char BMODULE_BEGIN   = '\u250C'; // ┌ BOX DRAWINGS LIGHT DOWN AND RIGHT     / ┏ \u250F HEAVY
	public static final char BMODULE_END     = '\u2510'; // ┐ BOX DRAWINGS LIGHT DOWN AND LEFT      /  ┓ \u2513 HEAVY
	public static final char SEPARATOR_BEGIN = '\u251C'; // ├ BOX DRAWINGS LIGHT VERTICAL AND RIGHT / ┣ \u2523 HEAVY
	public static final char SEPARATOR_END   = '\u2524'; // ┤ BOX DRAWINGS LIGHT VERTICAL AND LEFT  / ┫ \u252B HEAVY
	public static final char EMODULE_BEGIN   = '\u2514'; // └ BOX DRAWINGS LIGHT UP AND RIGHT       / ┗ \u2517 HEAVY
	public static final char EMODULE_END     = '\u2518'; // ┘ BOX DRAWINGS LIGHT UP AND LEFT        / ┛ \u251B HEAVY
	
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
//	private static final String ASCII_GLYPHS = "=<>()+-\\/#.|~";
	
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
