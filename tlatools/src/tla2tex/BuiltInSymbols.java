// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS BuiltInSymbols                                                     *
*                                                                          *
* Defines the TLA+ built-in symbols, their alignment classes, and how      *
* they are typeset.  Provides the following methods.                       *
*                                                                          *
*   Initialize()                                                           *
*     Must be called before any other methods of the class are             *
*     called.                                                              *
*                                                                          *
*   GetBuiltInSymbol(String str)                                           *
*     If str is a built-in TLA symbol, it returns the corresponding        *
*     Symbol object.  Otherwise, it returns null.                          *
*                                                                          *
*   IsBuiltInSymbol(String str)                                            *
*     True iff str is a built-in TLA symbol.                               *
*                                                                          *
*   IsBuiltInPrefix(String str)                                            *
*     True iff str is a non-empty prefix (possibly the entire string)      *
*     of a built-in TLA symbol that is not a string of letters (like       *
*     "ENABLED" or "WF_") and is not a "\\" (a backslash) followed by      *
*     a string of letters (like "\\cup").                                  *
*                                                                          *
*   IsStringChar(char c)                                                   *
*     True iff c is a character that can appear un-escaped (not            *
*     preceded by "\") in a TLA+ string.                                   *
*                                                                          *
* See the Symbol class for more information.                               *
***************************************************************************/
package tla2tex;
import java.util.Enumeration;
import java.util.Hashtable;

public final class BuiltInSymbols
  { 
    /***********************************************************************
    * The following six hash tables are built by the Initialize method.  *
    ***********************************************************************/
    private static Hashtable builtInHashTable = new Hashtable(200);
      /*********************************************************************
      * Maps built-in symbols (which are strings) to their Symbol          *
      * objects.  Does not contain PlusCal symbols.                        *
      *********************************************************************/

    private static Hashtable prefixHashTable  = new Hashtable(700);
      /*********************************************************************
      * A table containing the prefixes of all built-in symbols in         *
      * builtInHashTable.  (It holds only their keys.)                     *
      *********************************************************************/

    private static Hashtable pcalBuiltInHashTable = new Hashtable(200);
      /*********************************************************************
      * Maps built-in symbols (which are strings) to their Symbol          *
      * objects.  It includes the PlusCal symbols.                         *
      *********************************************************************/

    private static Hashtable pcalPrefixHashTable  = new Hashtable(700);
      /*********************************************************************
      * A table containing the prefixes of all built-in symbols in         *
      * pcalBuiltInHashTable.  (It holds only their keys.)                 *
      *********************************************************************/

    private static Hashtable stringCharTable  = new Hashtable(100);
      /*********************************************************************
      * A table of all the characters that may appear in a TLA+ string     *
      * token.                                                             *
      *********************************************************************/

    private static Hashtable canPrecedeLabelTable = new Hashtable(15);
      /*********************************************************************
      * A table of all the tokens (strings) that can precede a labeled     *
      * statement.                                                         *
      *********************************************************************/

    private static String nullString = "" ;
      /*********************************************************************
      * Some hash tables are used only to remember the keys; there is no   *
      * value attached to them.  However, the Hashtable class stores a     *
      * non-null object with each key.  This is the object we use.         *
      *********************************************************************/
      
    public static void Initialize()
      { buildHashTable(); 
        buildPrefixHashTable(); 
        buildStringCharTable();
        buildCanPrecedeLabelTable();
      } ;

    public static boolean IsBuiltInSymbol(String str) 
      { return (null != GetBuiltInSymbol(str)) ;
      } ;

    /**
     * Returns true iff str is a built-in symbol--either a TLA+ or
     * PlusCal symbol if pcalMode = true, or just a TLA+ symbol if
     * pcalMode = false.
     * 
     * @param str : The symbols ascii string.
     * @param pcalMode : true if looking for pcal symbols as well as TLA+ symbols.
     * @return
     */
    public static boolean IsBuiltInSymbol(String str, boolean pcalMode) 
      { return null != GetBuiltInSymbol(str, pcalMode)  ;
      } ;
    
      /**
       * Returns the built-in symbol with string str.  If pcalMode = false,
       * just return a TLA+ symbol; if pcalMode = true, return either a TLA+
       * or a PlusCal symbol.
       * @param str
       * @param pcalMode
       * @return
       */
    public static Symbol GetBuiltInSymbol(String str, boolean pcalMode)
      { Symbol sym ;
        if (pcalMode) { 
            sym = (Symbol) pcalBuiltInHashTable.get(str);
        }
        else {
            sym = (Symbol) builtInHashTable.get(str); 
        }
       
        if (sym == null || (sym.pcal && ! pcalMode)) {
            return null ;
        }
        return sym;
      } ;


    public static Symbol GetBuiltInSymbol(String str)
      { return (Symbol) builtInHashTable.get(str);
      } ;

    public static boolean IsBuiltInPrefix(String str)
      { return prefixHashTable.containsKey(str) ;
      } ;

    public static boolean IsBuiltInPrefix(String str, boolean pcal)
      { if (pcal) {
          return pcalPrefixHashTable.containsKey(str);
      }
        return prefixHashTable.containsKey(str) ;
      } ;

    public static boolean IsStringChar(char ch)
      { return stringCharTable.containsKey("" + ch) ;
      } ;

    public static boolean CanPrecedeLabel(String str) {
        return canPrecedeLabelTable.containsKey(str) ;
    }
      
    private static void buildStringCharTable() 
      { String legalChars = 
                 /**********************************************************
                 * Here are all the non-escaped characters that can        *
                 * appear in a TLA+ string.                                *
                 **********************************************************/
                    "abcdefghijklmnopqrstuvwxyz"
                  + "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                  + " ~!@#$%^&*()_-+={}[]|:;<,>.?/`'" 
                  + "0123456789" ;
        int n = 0 ;
        while (n < legalChars.length())
          { stringCharTable.put("" + legalChars.charAt(n), nullString);
            n = n + 1 ;
          }
      } ;

    private static void buildCanPrecedeLabelTable() {
        String[] canPrecedeLabel = 
           {";", ")", "{",  "begin", "do", "either", "or", "then", "else", "elsif"};
        for (int i = 0; i < canPrecedeLabel.length; i++) {
            canPrecedeLabelTable.put(canPrecedeLabel[i], nullString);
        }
    }
    private static void add(String tla, String tex, int stype, int atype)
      /*********************************************************************
      * Adds a non-PlusCal entry to the builtInHashTable and               *
      * pcalBuiltInHashTable.                                              *
      *********************************************************************/
      { builtInHashTable.put(tla, new Symbol(tla, tex, stype, atype) ) ; 
        pcalBuiltInHashTable.put(tla, new Symbol(tla, tex, stype, atype) ) ;   } ;


    private static void pcaladd(String tla, String tex, int stype, int atype)
      /*********************************************************************
      * Adds a PlusCal entry to the pcalBuiltInHashTable.                  *
      *********************************************************************/
      { pcalBuiltInHashTable.put(tla, new Symbol(tla, tex, stype, atype, true) ) ; } ;

    /*
     * The following special 1-character strings are for defining dummy
     * strings to represent special versions of the symbols "(", ")", "{"
     * and "}" that get printed differently from their normal versions.
     */
      public static String pcalLeftParen  = "" + '\0' ;
      public static String pcalRightParen = "" + '\1' ;
      public static String pcalLeftBrace  = "" + '\2' ;
      public static String pcalRightBrace = "" + '\3' ;

    private static void buildHashTable() 
      /*********************************************************************
      * Initializes builtInHashTable and pcalBuiltInHashTable.  This code  *
      * actually defines the                                               *
      * symbol and alignment types and the LaTeX input for each built-in   *
      * symbol.  It is required that, if two symbols have the same         *
      * alignment type, then their typeset versions have the same width.   *
      *                                                                    *
      * The LaTeX commands for all the infix symbols and some other        *
      * symbols are of the form \.{...}, where the \. command puts         *
      * \mbox{} before and after its argument.  This is necessary because  *
      * otherwise, TeX may vary the space around the symbol depending on   *
      * what comes before or after it, screwing up the alignment.          *
      *********************************************************************/
      { 
        add("_",          "\\_",             Symbol.KEYWORD, 0);
        add("ASSUMPTION", "{\\ASSUMPTION}",  Symbol.KEYWORD, 0);
        add("AXIOM",      "{\\AXIOM}",       Symbol.KEYWORD, 0);
        add("BOOLEAN",    "{\\BOOLEAN}",     Symbol.KEYWORD, 0);
        add("CASE",       "{\\CASE}",        Symbol.INFIX, 60); 
             // Changed to INFIX from KEYWORD by LL on 21 July 2012 to allow 
             // left-aligning with [].  It produces something reasonable when
             // a bunch of [] symbols are right-aligned with CASE as well.
        add("CONSTANT",   "{\\CONSTANT}",    Symbol.KEYWORD, 0);
        add("CONSTANTS",  "{\\CONSTANTS}",   Symbol.KEYWORD, 0);
        add("EXCEPT",     "{\\EXCEPT}",      Symbol.KEYWORD, 0);
        add("EXTENDS",    "{\\EXTENDS}",     Symbol.KEYWORD, 0);
        add("FALSE",      "{\\FALSE}",       Symbol.KEYWORD, 0);
        add("IF",         "{\\IF}",          Symbol.KEYWORD, 0);
        add("INSTANCE",   "{\\INSTANCE}",    Symbol.KEYWORD, 0);
        add("LOCAL",      "{\\LOCAL}",       Symbol.KEYWORD, 0);
        add("MODULE",     "{\\MODULE}",      Symbol.KEYWORD, 0);
        add("OTHER",      "{\\OTHER}",       Symbol.KEYWORD, 0);
        add("STRING",     "{\\STRING}",      Symbol.KEYWORD, 0);
        add("THEOREM",    "{\\THEOREM}",     Symbol.KEYWORD, 0);
        add("TRUE",       "{\\TRUE}",        Symbol.KEYWORD, 0);
        add("VARIABLE",   "{\\VARIABLE}",    Symbol.KEYWORD, 0);
        add("VARIABLES",  "{\\VARIABLES}",   Symbol.KEYWORD, 0);
        add("WITH",       "{\\WITH}",        Symbol.KEYWORD, 0);
// The following added for tla2tex
        add("BY",         "{\\BY}",          Symbol.KEYWORD, 0);
        add("OBVIOUS",    "{\\OBVIOUS}",     Symbol.KEYWORD, 0);
        add("HAVE",       "{\\HAVE}",        Symbol.KEYWORD, 0);
        add("QED",        "{\\QED}",         Symbol.KEYWORD, 0);
        add("TAKE",       "{\\TAKE}",        Symbol.KEYWORD, 0);
        add("DEF",        "{\\DEF}",         Symbol.KEYWORD, 0);
        add("HIDE",       "{\\HIDE}",        Symbol.KEYWORD, 0);
        add("RECURSIVE",  "{\\RECURSIVE}",   Symbol.KEYWORD, 0);
        add("USE",        "{\\USE}",         Symbol.KEYWORD, 0);
        add("DEFINE",     "{\\DEFINE}",      Symbol.KEYWORD, 0);
        add("PROOF",      "{\\PROOF}",       Symbol.KEYWORD, 0);
        add("WITNESS",    "{\\WITNESS}",     Symbol.KEYWORD, 0);
        add("PICK",       "{\\PICK}",        Symbol.KEYWORD, 0);
        add("DEFS",       "{\\DEFS}",        Symbol.KEYWORD, 0);
        add("SUFFICES",   "{\\SUFFICES}",    Symbol.KEYWORD, 0);
        add("NEW",        "{\\NEW}",         Symbol.KEYWORD, 0);
        add("LAMBDA",     "{\\LAMBDA}",      Symbol.KEYWORD, 0);
        add("STATE",      "{\\STATE}",       Symbol.KEYWORD, 0);
        add("ACTION",     "{\\ACTION}",      Symbol.KEYWORD, 0);
        add("TEMPORAL",   "{\\TEMPORAL}",    Symbol.KEYWORD, 0);
        add("ONLY",       "{\\ONLY}",        Symbol.KEYWORD, 0);  // added by LL on 2 Oct 2009
        add("OMITTED",    "{\\OMITTED}",     Symbol.KEYWORD, 0);  // added by LL on 31 Oct 2009
        add("ONLY",       "{\\ONLY}",        Symbol.KEYWORD, 0);  // added by LL on 2 Oct 2009
        add("LEMMA",      "{\\LEMMA}",       Symbol.KEYWORD, 0);  // added by LL on 22 Oct 2010
        add("PROPOSITION", "{\\PROPOSITION}", Symbol.KEYWORD, 0);  // added by LL on 22 Oct 2010
        add("COROLLARY",  "{\\COROLLARY}",   Symbol.KEYWORD, 0);  // added by LL on 22 Oct 2010
        add("WF_", "{\\WF}",        Symbol.SUBSCRIPTED, 0);
        add("SF_", "{\\SF}",        Symbol.SUBSCRIPTED, 0);
        add(">>_", "{\\rangle}",    Symbol.SUBSCRIPTED, 0);
        add("]_",  "]",           Symbol.SUBSCRIPTED, 0);

        add("(",   "(",           Symbol.LEFT_PAREN, 0);
        add("[",   "[",           Symbol.LEFT_PAREN, 0);
        add("{",   "\\{",         Symbol.LEFT_PAREN, 0);
        add("<<",  "{\\langle}",  Symbol.LEFT_PAREN, 0);

        add(")",   ")",           Symbol.RIGHT_PAREN, 0);
        add("}",   "\\}",         Symbol.RIGHT_PAREN, 0);
        add("]",   "]",           Symbol.RIGHT_PAREN, 0);
        add(">>",  "{\\rangle}",  Symbol.RIGHT_PAREN, 0);

        add("\\A",         "\\A\\,",          Symbol.PREFIX, 0);
        add("\\forall",    "\\forall\\,",     Symbol.PREFIX, 0);
        add("\\E",         "\\E\\,",          Symbol.PREFIX, 0);
        add("\\exists",    "\\exists\\,",     Symbol.PREFIX, 0);
        add("\\AA",        "{\\AA}",         Symbol.PREFIX, 0);
        add("\\EE",        "{\\EE}",         Symbol.PREFIX, 0);
        add("~",           "{\\lnot}",       Symbol.PREFIX, 0);
        add("\\lnot",      "{\\lnot}",       Symbol.PREFIX, 0);
        add("\\neg",       "{\\neg}",        Symbol.PREFIX, 0);
        add("<>",          "{\\Diamond}",    Symbol.PREFIX, 0);
        add("CHOOSE",      "{\\CHOOSE}",     Symbol.PREFIX, 0);
        add("ENABLED",     "{\\ENABLED}",    Symbol.PREFIX, 0);
        add("UNCHANGED",   "{\\UNCHANGED}",  Symbol.PREFIX, 0);
        add("SUBSET",      "{\\SUBSET}",     Symbol.PREFIX, 0);
        add("UNION",       "{\\UNION}",      Symbol.PREFIX, 0);
        add("DOMAIN",      "{\\DOMAIN}",     Symbol.PREFIX, 0);

        add("'",    "\\.{'}",            Symbol.POSTFIX, 0);
        add("^+",   "\\.{\\mbox{}^+}",   Symbol.POSTFIX, 0);
        add("^*",   "\\.{\\mbox{}^*}",   Symbol.POSTFIX, 0);
        add("^#",   "\\.{\\mbox{}^{\\#}}",   Symbol.POSTFIX, 0);


        add("=>",           "\\.{\\implies}",    Symbol.INFIX, 1);
        add("\\cdot",       "\\.{\\cdot}",       Symbol.INFIX, 2);
        add("<=>",          "\\.{\\equiv}",      Symbol.INFIX, 3);
        add("\\equiv",      "\\.{\\equiv}",      Symbol.INFIX, 4);
        add("~>",           "\\.{\\leadsto}",    Symbol.INFIX, 5);
        add("-+->",         "\\.{\\whileop}",    Symbol.INFIX, 6);

        add("\\subseteq",   "\\.{\\subseteq}",   Symbol.INFIX, 7); 
        add("\\subset",     "\\.{\\subset}",     Symbol.INFIX, 7); 
        add("\\supset",     "\\.{\\supset}",     Symbol.INFIX, 7); 
        add("\\supseteq",   "\\.{\\supseteq}",   Symbol.INFIX, 7); 

        add("\\ll",         "\\.{\\ll}",         Symbol.INFIX, 8);
        add("\\gg",         "\\.{\\gg}",         Symbol.INFIX, 8);
          /*****************************************************************
          * \ll and \gg not aligned with = and < because they are wider,   *
          * and they're not used enough to bother accommodating aligned    *
          * infix symbols of different widths.  However, this might now    * 
          * work because of changes made to handle PlusCal labels          *
          * essentially as infix operators.                                *
          *****************************************************************/
          
        add("\\",           "\\.{\\,\\backslash\\,}",  Symbol.INFIX, 9);
        add("\\cap",        "\\.{\\cap}",        Symbol.INFIX, 10);
        add("\\intersect",  "\\.{\\cap}",        Symbol.INFIX, 11);
        add("\\cup",        "\\.{\\cup}",        Symbol.INFIX, 12);
        add("\\union",      "\\.{\\cup}",        Symbol.INFIX, 13);
        add("/\\",          "\\.{\\land}",       Symbol.INFIX, 14);
        add("\\/",          "\\.{\\lor}",        Symbol.INFIX, 15);
        add("\\land",       "\\.{\\land}",       Symbol.INFIX, 16);
        add("\\lor",        "\\.{\\lor}",        Symbol.INFIX, 17);
        add("\\X",          "\\.{\\times}",      Symbol.INFIX, 18);
        add("-",            "\\.{-}",            Symbol.INFIX, 19);
        add("+",            "\\.{+}",            Symbol.INFIX, 19);
        add("*",            "\\.{*}",            Symbol.INFIX, 20);
        add("/",            "\\.{/}",            Symbol.INFIX, 21);
        add("^",            "\\.{\\ct}",         Symbol.INFIX, 22);
        add("|",            "\\.{\\,|\\,}",      Symbol.INFIX, 23);
        add("||",           "\\.{\\p@barbar}",   Symbol.INFIX, 24); // modified for PlusCal
        add("&",            "\\.{\\,\\&\\,}",    Symbol.INFIX, 25);
        add("&&",           "\\.{\\,\\&\\&\\,}", Symbol.INFIX, 26);
        add("++",           "\\.{\\pp}",         Symbol.INFIX, 27);
        add("--",           "\\.{\\mm}",         Symbol.INFIX, 27);
        add("**",           "\\.{\\stst}",       Symbol.INFIX, 28);
        add("//",           "\\.{\\slsl}",       Symbol.INFIX, 29);
        add("^^",           "\\.{\\ct\\ct}",     Symbol.INFIX, 30);
        add("|-",           "\\.{\\vdash}",      Symbol.INFIX, 31);
        add("|=",           "\\.{\\models}",     Symbol.INFIX, 32);
        add("-|",           "\\.{\\dashv}",      Symbol.INFIX, 33);
        add("=|",           "\\.{\\eqdash}",     Symbol.INFIX, 34);
        add("<:",           "\\.{\\ltcolon}",    Symbol.INFIX, 35);
        add(":>",           "\\.{\\colongt}",    Symbol.INFIX, 35);
        add(":=",           "\\.{:=}",           Symbol.INFIX, 35);
        add("::=",          "\\.{::=}",          Symbol.INFIX, 36);

        add("(+)",          "\\.{\\oplus}",      Symbol.INFIX, 37); 
        add("(-)",          "\\.{\\ominus}",     Symbol.INFIX, 37); 
        add("\\oplus",      "\\.{\\oplus}",      Symbol.INFIX, 37); 
        add("\\ominus",     "\\.{\\ominus}",     Symbol.INFIX, 37); 

        add("(.)",          "\\.{\\odot}",       Symbol.INFIX, 38);
        add("\\odot",       "\\.{\\odot}",       Symbol.INFIX, 38);

        add("(/)",          "\\.{\\oslash}",     Symbol.INFIX, 39);
        add("\\oslash",     "\\.{\\oslash}",     Symbol.INFIX, 39);

        add("(\\X)",        "\\.{\\otimes}",     Symbol.INFIX, 40);
        add("\\otimes",     "\\.{\\otimes}",     Symbol.INFIX, 40);

        add("\\uplus",      "\\.{\\uplus}",      Symbol.INFIX, 41);
        add("\\sqcap",      "\\.{\\sqcap}",      Symbol.INFIX, 42);
        add("\\sqcup",      "\\.{\\sqcup}",      Symbol.INFIX, 43);
        add("\\div",        "\\.{\\div}",        Symbol.INFIX, 44);
        add("\\star",       "\\.{\\star}",       Symbol.INFIX, 45);

        add("\\o",          "\\.{\\circ}",       Symbol.INFIX, 46);
        add("\\circ",       "\\.{\\circ}",       Symbol.INFIX, 46);

        add("\\bigcirc",    "\\.{\\bigcirc}",    Symbol.INFIX, 47);
        add("\\bullet",     "\\.{\\bullet}",     Symbol.INFIX, 48);

        add("\\in",         "\\.{\\in}",         Symbol.INFIX, 49);
        add("\\notin",      "\\.{\\notin}",      Symbol.INFIX, 49);
        add("=",            "\\.{=}",            Symbol.INFIX, 49);
        add("#",            "\\.{\\neq}",        Symbol.INFIX, 49);
        add("/=",           "\\.{\\neq}",        Symbol.INFIX, 49);
        add("<",            "\\.{<}",            Symbol.INFIX, 49);
        add(">",            "\\.{>}",            Symbol.INFIX, 49);
        add("<=",           "\\.{\\leq}",        Symbol.INFIX, 49);
        add("=<",           "\\.{\\leq}",        Symbol.INFIX, 49);
        add(">=",           "\\.{\\geq}",        Symbol.INFIX, 49);
        add("\\prec",       "\\.{\\prec}",       Symbol.INFIX, 49);
        add("\\succ",       "\\.{\\succ}",       Symbol.INFIX, 49);
        add("\\preceq",     "\\.{\\preceq}",     Symbol.INFIX, 49);
        add("\\succeq",     "\\.{\\succeq}",     Symbol.INFIX, 49);
        add("\\sim",        "\\.{\\sim}",        Symbol.INFIX, 49);
        add("\\simeq",      "\\.{\\simeq}",      Symbol.INFIX, 49);
        add("\\approx",     "\\.{\\approx}",     Symbol.INFIX, 49);
        add("\\doteq",      "\\.{\\doteq}",      Symbol.INFIX, 49);

        add("\\asymp",      "\\.{\\asymp}",      Symbol.INFIX, 50);

        add("\\sqsubset",   "\\.{\\sqsubset}",   Symbol.INFIX, 51);
        add("\\sqsupset",   "\\.{\\sqsupset}",   Symbol.INFIX, 51);
        add("\\sqsubseteq", "\\.{\\sqsubseteq}", Symbol.INFIX, 51);
        add("\\sqsupseteq", "\\.{\\sqsupseteq}", Symbol.INFIX, 51);

        add("\\propto",     "\\.{\\propto}",     Symbol.INFIX, 52);
        add(":",            "\\.{:}",            Symbol.PUNCTUATION, 53);
        add("->",           "\\.{\\rightarrow}", Symbol.INFIX, 54);
        add("|->",          "\\.{\\mapsto}",     Symbol.INFIX, 55);
        add("<-",           "\\.{\\leftarrow}",  Symbol.INFIX, 56);
        add("==",           "\\.{\\defeq}",      Symbol.INFIX, 57);

        add("ELSE",         "\\.{\\ELSE}",       Symbol.PREFIX, 58); 
        add("THEN",         "\\.{\\THEN}",       Symbol.PREFIX, 58); 
        add("LET",          "\\.{\\LET}",        Symbol.INFIX, 59); // Changed by LL  on 21 Jul 22
        add("IN",          "\\.{\\IN}",          Symbol.INFIX, 59); //    from PREFIX to fix alignment bug
        add("[]",          "{\\Box}",            Symbol.INFIX, 60); // Changed from PREFIX to left-align with CASE
        add("::",          "{\\coloncolon}",     Symbol.INFIX,  61);
        add("ASSUME",      "{\\ASSUME}",         Symbol.KEYWORD, 62);
        add("PROVE",       "{\\PROVE}",          Symbol.KEYWORD, 62);


        add("..",           "\\.{\\dotdot}",     Symbol.INFIX, 0);
        add("...",          "\\.{\\dots}",       Symbol.INFIX, 0);
        add("$",            "\\.{\\,\\$\\,}",    Symbol.INFIX, 0);
        add("$$",           "\\.{\\,\\$\\$\\,}", Symbol.INFIX, 0);
        add("?",            "\\.{?}",            Symbol.INFIX, 0);
        add("??",           "\\.{\\,??\\,}",     Symbol.INFIX, 0);
        add("%",            "\\.{\\%}",          Symbol.INFIX, 0);
        add("%%",           "\\.{\\,\\%\\%\\,}", Symbol.INFIX, 0);
        add("##",           "\\.{\\,\\#\\#\\,}", Symbol.INFIX, 0);
        add("@@",           "\\.{\\,@@\\,}",     Symbol.INFIX, 0);
        add("!!",           "\\.{!!}",           Symbol.INFIX, 0);
        add("\\times",      "\\.{\\times}",      Symbol.INFIX, 0);
        add("\\leq",        "\\.{\\leq}",        Symbol.INFIX, 0);
        add("\\geq",        "\\.{\\geq}",        Symbol.INFIX, 0);
        add("\\mod",        "\\.{\\%}",          Symbol.INFIX, 0);
        add("\\wr",         "\\.{\\wr}",         Symbol.INFIX, 0);
        add("\\cong",       "\\.{\\cong}",       Symbol.INFIX, 0);
        add("!",            "{\\bang}",          Symbol.INFIX, 0);

        add(",",   ",\\,",   Symbol.PUNCTUATION, 0);
        add(".",   ".",     Symbol.PUNCTUATION, 0);

        add("-.",  "\\.{-\\!.\\,}",    Symbol.MISC, 0);
        add("@",  "@",      Symbol.MISC, 0);
        
        // The following are added for PlusCal
        pcaladd("fair",      "{\\p@fair}",       Symbol.KEYWORD,     0);
        pcaladd("algorithm", "{\\p@algorithm}",  Symbol.KEYWORD,     0);
        pcaladd("--fair",    "{\\p@mmfair}",     Symbol.KEYWORD,     0);
        pcaladd("--algorithm", "{\\p@mmalgorithm}",  Symbol.KEYWORD,     0);
        pcaladd(";",          "{\\p@semicolon}",  Symbol.PUNCTUATION, 63);
        pcaladd("assert",     "{\\p@assert}",     Symbol.KEYWORD,     0);
        pcaladd("await",      "{\\p@await}",      Symbol.KEYWORD,     0);
        pcaladd("begin",      "{\\p@begin}",      Symbol.KEYWORD,     0);
        pcaladd("end",        "{\\p@end}",        Symbol.KEYWORD,     0);
        pcaladd("call",       "{\\p@call}",       Symbol.KEYWORD,     0);
        pcaladd("define",     "{\\p@define}",     Symbol.KEYWORD,     0);
        pcaladd("do",         "{\\p@do}",         Symbol.KEYWORD,     0);
        pcaladd("either",     "{\\p@either}",     Symbol.INFIX,       64); // not sure
        pcaladd("or",         "{\\p@or}",         Symbol.INFIX,       64); // not sure
        pcaladd("goto",       "{\\p@goto}",       Symbol.KEYWORD,     0);
        pcaladd("if",         "{\\p@if}",         Symbol.KEYWORD,     0);
        pcaladd("then",       "{\\p@then}",       Symbol.INFIX,       65); 
        pcaladd("else",       "{\\p@else}",       Symbol.INFIX,       65); 
        pcaladd("elsif",      "{\\p@elsif}",      Symbol.INFIX,       65); 
          // I tried making "then", "else", and "elsif" KEYWORDS that all
          // had the same width when printed.  This didn't work because
          // of the extra letter in "elsif", so if the statements that follow
          // them are aligned, then TLATeX adds extra space after an "else" or
          // "then" because of the extra space between it and what follows.
          // Making them INFIX with the same alignment value produces some
          // bogus alignments, but it seems to be the lesser evil.
        pcaladd("macro",      "{\\p@macro}",      Symbol.KEYWORD,     0);
        pcaladd("print",      "{\\p@print}",      Symbol.KEYWORD,     0);
        pcaladd("procedure",  "{\\p@procedure}",  Symbol.KEYWORD,     0);
        pcaladd("process",    "{\\p@process}",    Symbol.KEYWORD,     0);
        pcaladd("return",     "{\\p@return}",     Symbol.KEYWORD,     0);
        pcaladd("skip",       "{\\p@skip}",       Symbol.KEYWORD,     0);
        pcaladd("variable",   "{\\p@variable}",   Symbol.KEYWORD,     0);
        pcaladd("variables",  "{\\p@variables}",  Symbol.KEYWORD,     0);
        pcaladd("while",      "{\\p@while}",      Symbol.KEYWORD,     0);
        pcaladd("with",       "{\\p@with}",       Symbol.KEYWORD,     0);
        pcaladd("when",       "{\\p@when}",       Symbol.KEYWORD,     0);

        // The following are the symbols for the PlusCal delimiters:
        //       "("  ")"  "{"  "}"  
        pcaladd(pcalLeftParen,  "{\\p@lparen}",   Symbol.LEFT_PAREN,  0);
        pcaladd(pcalRightParen, "{\\p@rparen}",   Symbol.RIGHT_PAREN, 0);
        pcaladd(pcalLeftBrace,  "{\\p@lbrace}",   Symbol.LEFT_PAREN,  0);
        pcaladd(pcalRightBrace, "{\\p@rbrace}",  Symbol.RIGHT_PAREN, 0);

      } ;      


    private static void buildPrefixHashTable() 
      /*********************************************************************
      * Initializes prefixHashTable and pcalPrefixHashTable, assuming that *
      * builtInHashTable and pcalBuiltInHashTable are already initialize   *
      *********************************************************************/
      { Enumeration builtInEnum = builtInHashTable.keys();
        while (builtInEnum.hasMoreElements())
          { String symbol = (String) builtInEnum.nextElement();
            if (    Misc.IsLetter(symbol.charAt(0))
                 ||    (symbol.length() > 1)
                    && (symbol.charAt(0) == '\\')
                    && Misc.IsLetter(symbol.charAt(1)))
              { /***********************************************************
                * Should not put prefixes of this symbol in                *
                * prefixHashTable.                                         *
                ***********************************************************/
              }
            else
              { /***********************************************************
                * Put symbol and all its prefixes in prefixHashTable.      *
                ***********************************************************/
                while (symbol.length() > 0)                              
                 { prefixHashTable.put(symbol, nullString);             
                   symbol = symbol.substring(0, symbol.length() - 1);   
                 } ;                                                    
              } ;
          }
        builtInEnum = pcalBuiltInHashTable.keys();
        while (builtInEnum.hasMoreElements())
          { String symbol = (String) builtInEnum.nextElement();
            if (    Misc.IsLetter(symbol.charAt(0))
                 ||    (symbol.length() > 1)
                    && (symbol.charAt(0) == '\\')
                    && Misc.IsLetter(symbol.charAt(1)))
              { /***********************************************************
                * Should not put prefixes of this symbol in                *
                * prefixHashTable.                                         *
                ***********************************************************/
              }
            else
              { /***********************************************************
                * Put symbol and all its prefixes in prefixHashTable.      *
                ***********************************************************/
                while (symbol.length() > 0)                              
                 { pcalPrefixHashTable.put(symbol, nullString);             
                   symbol = symbol.substring(0, symbol.length() - 1);   
                 } ;                                                    
              } ;
          }
      }

   }  

/* last modified on Sat 22 Sep 2007 at  8:44:43 PST by lamport */
