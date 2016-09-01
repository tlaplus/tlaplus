package tla2unicode;

public final class UnicodeConstants {
	private UnicodeConstants() {}
	
	// Mathematical/logic symbols
	
	public static final char DELTA_EQUAL_TO      = '\u225C'; // ≜
	public static final char LEFTWARDS_ARROW     = '\u2190'; // ←
	public static final char RIGHTWARDS_ARROW    = '\u2192'; // → 
	public static final char MAPS_TO             = '\u21A6'; // ↦ RIGHTWARDS ARROW FROM BAR
	public static final char LEFT_ANGLE_BRACKET  = '\u27E8'; // ⟨ MATHEMATICAL LEFT ANGLE BRACKET
    public static final char RIGHT_ANGLE_BRACKET = '\u27E9'; // ⟩ MATHEMATICAL RIGHT ANGLE BRACKET
	public static final char RIGHTWARDS_WAVE_ARROW = '\u219D'; // ↝ \u219D
	public static final char RIGHTWARDS_ARROW_PLUS = '\u2945'; // ⥅ RIGHTWARDS ARROW WITH PLUS BELOW
	public static final char PRIME     = '\u2032'; // ′ 
	public static final char FORALL    = '\u2200'; // ∀ FOR ALL
	public static final char EXISTS    = '\u2203'; // ∃ THERE EXISTS
	public static final char NOT       = '\u00ac'; // ¬ NOT SIGN
	public static final char AND       = '\u2227'; // ∧ LOGICAL AND 
	public static final char OR        = '\u2228'; // ∨ LOGICAL OR
	public static final char IMPLIES   = '\u21D2'; // ⇒ RIGHTWARDS DOUBLE ARROW
	public static final char IDENT     = '\u2261'; // ≡ IDENTICAL TO
	public static final char IFF       = '\u21D4'; // ⇔ LEFT RIGHT DOUBLE ARROW
	public static final char NEQUAL    = '\u2260'; // ≠ NOT EQUAL TO
    public static final char ELEM      = '\u2208';  // ∈ ELEMENT OF
	public static final char NELEM     = '\u2209'; // ∉ NOT AN ELEMENT OF
	public static final char SUBSET    = '\u2282'; // ⊂ SUBSET OF
	public static final char SUBSETEQ  = '\u2286'; // ⊆ SUBSET OF OR EQUAL TO
	public static final char SUPSET    = '\u2283'; // ⊃ SUPERSET OF
	public static final char SUPSETEQ  = '\u2287'; // ⊇ SUPERSET OF OR EQUAL TO
	public static final char NSUBSET   = '\u2284'; // ⊄ NOT A SUBSET OF	
	public static final char NSUPSET   = '\u2285'; // ⊅ NOT A SUPERSET OF
	public static final char NSUBSETEQ = '\u2288'; // ⊈ NEITHER A SUBSET OF NOR EQUAL TO
	public static final char NSUPSETEQ = '\u2289'; // ⊉ NEITHER A SUPERSET OF NOR EQUAL TO
	public static final char XION      = '\u2229'; // ∩ INTERSECTION
	public static final char UNION     = '\u222A'; // ∪ UNION
	public static final char UPLUS     = '\u228E'; // ⊎ MULTISET UNION
	public static final char EMPTY_SET = '\u2205'; // ∅ EMPTY SET

    public static final char LEQ  = '\u2264'; // ≤ LESS-THAN OR EQUAL TO
	public static final char GEQ  = '\u2265'; // ≥ GREATER-THAN OR EQUAL TO
	public static final char LTLT = '\u226A'; // ≪ MUCH LESS-THAN
	public static final char GTGT = '\u226B'; // ≫ MUCH GREATER-THAN
	
	public static final char MULT = '\u00D7'; // × MULTIPLICATION SIGN
	public static final char DIV  = '\u00F7'; // ÷ DIVISION SIGN
	public static final char DOT  = '\u22C5'; // ⋅ DOT OPERATOR
	
	public static final char OPLUS  = '\u2295'; // ⊕ CIRCLED PLUS
	public static final char OMINUS = '\u2296'; // ⊖ CIRCLED MINUS
	public static final char OTIMES = '\u2297'; // ⊗ CIRCLED TIMES
    public static final char OSLASH = '\u2298'; // ⊘ CIRCLED DIVISION SLASH
	public static final char ODOT   = '\u2299'; // ⊙ CIRCLED DOT OPERATOR
		
	public static final char PREC    = '\u227A'; // ≺ PRECEDES
	public static final char PRECEQ  = '\u227C'; // ≼ PRECEDES OR EQUAL TO
	public static final char SUCC    = '\u227B'; // ≻ SUCCEEDS
	public static final char SUCCEQ  = '\u227D'; // ≽ SUCCEEDS OR EQUAL TO
	
	public static final char SQSUB   = '\u228F'; // ⊏ SQUARE IMAGE OF
	public static final char SQSUBEQ = '\u2291'; // ⊑ SQUARE IMAGE OF OR EQUAL TO
	public static final char SQSUP   = '\u2290'; // ⊐ SQUARE ORIGINAL OF
	public static final char SQSUPEQ = '\u2292'; // ⊒ SQUARE ORIGINAL OF OR EQUAL TO
	public static final char SQCAP   = '\u2293'; // ⊓ SQUARE CAP
	public static final char SQCUP   = '\u2294'; // ⊔ SQUARE CUP
	
	public static final char RING    = '\u2218'; // ∘ RING OPERATOR	
	public static final char BULLET  = '\u2022'; // • 
	public static final char STAR    = '\u22c6'; // ⋆ STAR OPERATOR
	public static final char LARGE_CIRCLE = '\u25EF'; // ◯

	public static final char WREATH   = '\u2240'; // ≀ WREATH PRODUCT
	public static final char APPROXEQ = '\u2245'; // ≅ APPROXIMATELY EQUAL TO
	public static final char PROPTO   = '\u221D'; // ∝ PROPORTIONAL TO
	public static final char APPROX   = '\u2248'; // ≈ ALMOST EQUAL TO
	public static final char DOTEQ    = '\u2250'; // ≐ APPROACHES THE LIMIT
	public static final char SIMEQ    = '\u2243'; // ≃ ASYMPTOTICALLY EQUAL TO
	public static final char PAR      = '\u2016'; // ‖ DOUBLE VERTICAL LINE
	public static final char FULLWIDTH_TILDE = '\uFF5E'; // ～ FULLWIDTH TILDE
	public static final char SIM_MINUS_SIM   = '\u2A6C'; // ⩬ SIMILAR MINUS SIMILAR
	public static final char EQUIVALENT_TO   = '\u224D'; // ≍ EQUIVALENT TO
	public static final char RATIO      = '\u2236'; // ∶ RATIO
	public static final char PROPORTION = '\u2237'; // ∷ PROPORTION
	
	public static final char TURNSTILE             = '\u22A2'; // ⊢ RIGHT TACK
	public static final char LEFT_TURNSTILE        = '\u22A3'; // ⊣ LEFT TACK 
	public static final char BOTTOM                = '\u22a5'; // ⊥ UP TACK \bottom 
	public static final char TOP                   = '\u22a4'; // ⊤ DOWN TACK \top 
	public static final char DOUBLE_TURNSTILE      = '\u22A8'; // ⊨ TRUE
	public static final char DOUBLE_LEFT_TURNSTILE = '\u2AE4'; // ⫤ VERTICAL BAR DOUBLE LEFT TURNSTILE
	
	public static final char WHITE_SQUARE        = '\u25A1';  // □ WHITE SQUARE
	public static final char WHITE_MEDIUM_SQUARE = '\u25FB';  // ◻ WHITE MEDIUM SQUARE

	public static final char WHITE_DIAMOND        = '\u25C7'; // ◇ WHITE DIAMOND
	public static final char WHITE_MEDIUM_DIAMOND = '\u2B26'; // ⬦ WHITE MEDIUM DIAMOND
	public static final char DIAMOND_OPERATOR     = '\u22C4'; // ⋄ DIAMOND OPERATOR

	public static final char SUBGROUP   = '\u22B2'; // ⊲ NORMAL SUBGROUP OF
	public static final char SUPGROUP   = '\u22B3'; // ⊳ CONTAINS AS NORMAL SUBGROUP
	public static final char SUBGROUPEQ = '\u22B4'; // ⊴ NORMAL SUBGROUP OF OR EQUAL TO
	public static final char SUPGROUPEQ = '\u22B5'; // ⊵ CONTAINS AS NORMAL SUBGROUP OR EQUAL TO
	public static final char DOUBLE_COLON_EQUAL = '\u2A74'; // ⩴ DOUBLE COLON EQUAL
	public static final char COLON_EQUAL        = '\u2254'; // ≔ COLON EQUALS
	
	public static final char SUM        = '\u2211'; // ∑ N-ARY SUMMATION
	public static final char PRODUCT    = '\u220F'; // ∏ N-ARY PRODUCT
	public static final char NARY_AND   = '\u22C0'; // ⋀ N-ARY LOGICAL AND
	public static final char NARY_OR    = '\u22C1'; // ⋁ N-ARY LOGICAL OR
	public static final char NARY_CAP   = '\u22C2'; // ⋂ N-ARY INTERSECTION
	public static final char NARY_CUP   = '\u22C3'; // ⋃ N-ARY UNION
	public static final char NARY_UPLUS = '\u2A04'; // ⨄ N-ARY UNION OPERATOR WITH PLUS
		
	public static final char DOUBLE_STRUCK_N   = '\u2115'; // ℕ DOUBLE-STRUCK CAPITAL N
	public static final char DOUBLE_STRUCK_Z   = '\u2124'; // ℤ DOUBLE-STRUCK CAPITAL Z
	public static final char DOUBLE_STRUCK_Q   = '\u211A'; // ℚ DOUBLE-STRUCK CAPITAL Q
	public static final char DOUBLE_STRUCK_R   = '\u211D'; // ℝ DOUBLE-STRUCK CAPITAL R	
	
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

	public static final char SUBSCRIPT_PLUS = '\u208A';     // ₊ SUBSCRIPT PLUS SIGN
	public static final char SUBSCRIPT_ASTERISK = '\u204E'; // ⁎ LOW ASTERISK
	
	// Superscripts
	
	private static final char[] SUPERSCRIPT_DIGIT = { 
			'\u2070', '\u00B9', '\u00B2', '\u00B3', '\u2074', '\u2075', '\u2076', '\u2077', '\u2078', '\u2079'
		};

	public static final char superscriptDigit(int num) { // ⁰¹²³⁴⁵⁶⁷⁸⁹
		assert num >= 0 && num <= 9;
		return SUPERSCRIPT_DIGIT[num];
	}	
	
	public static final char SUPERSCRIPT_PLUS = '\u207A'; // ⁺ SUPERSCRIPT PLUS SIGN 

	// Box drawing

	public static final char HORIZONTAL         = '\u2500'; // ─ BOX DRAWINGS LIGHT HORIZONTAL
	public static final char DOWN_AND_RIGHT     = '\u250C'; // ┌ BOX DRAWINGS LIGHT DOWN AND RIGHT
	public static final char DOWN_AND_LEFT      = '\u2510'; // ┐ BOX DRAWINGS LIGHT DOWN AND LEFT
	public static final char VERTICAL_AND_RIGHT = '\u251C'; // ├ BOX DRAWINGS LIGHT VERTICAL AND RIGHT
	public static final char VERTICAL_AND_LEFT  = '\u2524'; // ┤ BOX DRAWINGS LIGHT VERTICAL AND LEFT
	public static final char UP_AND_RIGHT       = '\u2514'; // └ BOX DRAWINGS LIGHT UP AND RIGHT
	public static final char UP_AND_LEFT        = '\u2518'; // ┘ BOX DRAWINGS LIGHT UP AND LEFT
	
	public static final char HEAVY_HORIZONTAL         = '\u2501'; // ━ BOX DRAWINGS HEAVY HORIZONTAL
	public static final char HEAVY_DOWN_AND_RIGHT     = '\u250F'; // ┏ BOX DRAWINGS HEAVY DOWN AND RIGHT
	public static final char HEAVY_DOWN_AND_LEFT      = '\u2513'; // ┓ BOX DRAWINGS HEAVY DOWN AND LEFT
	public static final char HEAVY_VERTICAL_AND_RIGHT = '\u2523'; // ┣ BOX DRAWINGS HEAVY VERTICAL AND RIGHT
	public static final char HEAVY_VERTICAL_AND_LEFT  = '\u252B'; // ┫ BOX DRAWINGS HEAVY VERTICAL AND LEFT
	public static final char HEAVY_UP_AND_RIGHT       = '\u2517'; // ┗ BOX DRAWINGS HEAVY UP AND RIGHT
	public static final char HEAVY_UP_AND_LEFT        = '\u251B'; // ┛ BOX DRAWINGS HEAVY UP AND LEFT
	
	// Extended brackets
	
	public static final char LEFT_PARENTHESES_UPPER_HOOK  = '\u239B'; // ⎛ LEFT PARENTHESIS UPPER HOOK
	public static final char LEFT_PARENTHESES_EXTENSION   = '\u239C'; // ⎜ LEFT PARENTHESIS EXTENSION
	public static final char LEFT_PARENTHESES_LOWER_HOOK  = '\u239D'; // ⎝ LEFT PARENTHESIS LOWER HOOK
	public static final char RIGHT_PARENTHESES_UPPER_HOOK = '\u239E'; // ⎞ RIGHT PARENTHESIS UPPER HOOK
	public static final char RIGHT_PARENTHESES_EXTENSION  = '\u239F'; // ⎟ RIGHT PARENTHESIS EXTENSION
	public static final char RIGHT_PARENTHESES_LOWER_HOOK = '\u23A0'; // ⎠ RIGHT PARENTHESIS LOWER HOOK

	public static final char LEFT_SQUARE_BRACKET_UPPER_CORNER  = '\u23A1'; // ⎡ LEFT SQUARE BRACKET UPPER CORNER
	public static final char LEFT_SQUARE_BRACKET_EXTENSION     = '\u23A2'; // ⎢ LEFT SQUARE BRACKET EXTENSION
	public static final char LEFT_SQUARE_BRACKET_LOWER_CORNER  = '\u23A3'; // ⎣ LEFT SQUARE BRACKET LOWER CORNER
	public static final char RIGHT_SQUARE_BRACKET_UPPER_CORNER = '\u23A4'; // ⎤ RIGHT SQUARE BRACKET UPPER CORNER
	public static final char RIGHT_SQUARE_BRACKET_EXTENSION    = '\u23A5'; // ⎥ RIGHT SQUARE BRACKET EXTENSION
	public static final char RIGHT_SQUARE_BRACKET_LOWER_CORNER = '\u23A6'; // ⎦ RIGHT SQUARE BRACKET LOWER CORNER

	public static final char LEFT_BRACE_UPPER_HOOK    = '\u23A7'; // ⎧ LEFT CURLY BRACKET UPPER HOOK
	public static final char LEFT_BRACE_MIDDLE_PIECE  = '\u23A8'; // ⎨ LEFT CURLY BRACKET MIDDLE PIECE
	public static final char LEFT_BRACE_LOWER_HOOK    = '\u23A9'; // ⎩ LEFT CURLY BRACKET LOWER HOOK
	public static final char RIGHT_BRACE_UPPER_HOOK   = '\u23AB'; // ⎫ RIGHT CURLY BRACKET UPPER HOOK
	public static final char RIGHT_BRACE_MIDDLE_PIECE = '\u23AC'; // ⎬ RIGHT CURLY BRACKET MIDDLE PIECE
	public static final char RIGHT_BRACE_LOWER_HOOK   = '\u23AD'; // ⎭ RIGHT CURLY BRACKET LOWER HOOK
	public static final char BRACE_EXTENSION          = '\u23AA'; // ⎪ CURLY BRACKET EXTENSION	
}
