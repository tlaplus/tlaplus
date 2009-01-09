/***************************************************************************
* CLASS PcalBuiltInSymbols                                                 *
*                                                                          *
* THIS IS A VERSION OF tlatex.BuiltInSymbols MODIFIED TO ADD ";" AS A      *
* BUILTIN SYMBOL, AND TO MAKE "]_" and ">>_" SYMBOLS OF TYPE               *
* "RIGHT_PAREN".                                                           *
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
package pcal;
import java.util.Enumeration;
import java.util.Hashtable;

import tla2tex.Misc;
import tla2tex.Symbol;

public final class PcalBuiltInSymbols
  { 
    /***********************************************************************
    * The following three hash tables are built by the Initialize method.  *
    ***********************************************************************/
    private static Hashtable builtInHashTable = new Hashtable(200);
      /*********************************************************************
      * Maps built-in symbols (which are strings) to their Symbol          *
      * objects.                                                           *
      *********************************************************************/

    private static Hashtable prefixHashTable  = new Hashtable(700);
      /*********************************************************************
      * A table containing the prefixes of all built-in symbols.  (It      *
      * holds only their keys.)                                            *
      *********************************************************************/

    private static Hashtable stringCharTable  = new Hashtable(100);
      /*********************************************************************
      * A table of all the characters that may appear in a TLA+ string     *
      * token.                                                             *
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
      } ;

    public static boolean IsBuiltInSymbol(String str) 
      { return (null != GetBuiltInSymbol(str)) ;
      } ;

    public static Symbol GetBuiltInSymbol(String str)
      { return (Symbol) builtInHashTable.get(str);
      } ;

    public static boolean IsBuiltInPrefix(String str)
      { return prefixHashTable.containsKey(str) ;
      } ;

    public static boolean IsStringChar(char ch)
      { return stringCharTable.containsKey("" + ch) ;
      } ;

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

    private static void add(String tla, String tex, int stype, int atype)
      /*********************************************************************
      * Adds an entry to the builtInHashTable.                             *
      *********************************************************************/
      { builtInHashTable.put(tla, new Symbol(tla, tex, stype, atype) ) ; } ;


    private static void buildHashTable() 
      /*********************************************************************
      * Initializes builtInHashTable.  This code actually defines the      *
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
        add("ASSUME",     "{\\ASSUME}",      Symbol.KEYWORD, 0);
        add("ASSUMPTION", "{\\ASSUMPTION}",  Symbol.KEYWORD, 0);
        add("AXIOM",      "{\\AXIOM}",       Symbol.KEYWORD, 0);
        add("BOOLEAN",    "{\\BOOLEAN}",     Symbol.KEYWORD, 0);
        add("CASE",       "{\\CASE}",        Symbol.KEYWORD, 0);
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

        add("WF_", "{\\WF}",        Symbol.SUBSCRIPTED, 0);
        add("SF_", "{\\SF}",        Symbol.SUBSCRIPTED, 0);
        add(">>_", "{\\rangle}",    Symbol.RIGHT_PAREN, 0);
        add("]_",  "]",             Symbol.RIGHT_PAREN, 0);

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
          * and they're not used enough to bother accomodating.            *
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
        add("||",           "\\.{\\,||\\,}",     Symbol.INFIX, 24);
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
        add("=<",           "\\.{\\leq}",        Symbol.INFIX, 49);
        add("<=",           "\\.{\\leq}",        Symbol.INFIX, 49);
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
        add("LET",          "\\.{\\LET}",        Symbol.PREFIX, 59);
        add("IN",          "\\.{\\IN}",          Symbol.PREFIX, 59);
        add("[]",          "{\\Box}",            Symbol.PREFIX, 60);

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
        add("!",            "!",                 Symbol.INFIX, 0);

        add(";",   ";",     Symbol.PUNCTUATION, 0);
        add(",",   ",\\,",   Symbol.PUNCTUATION, 0);
        add(".",   ".",     Symbol.PUNCTUATION, 0);

        add("-.",  "\\.{-\\!.\\,}",    Symbol.MISC, 0);
        add("@",  "@",      Symbol.MISC, 0);

      } ;      


    private static void buildPrefixHashTable() 
      /*********************************************************************
      * Initializes prefixHashTable, assuming that builtInHashTable is     *
      * already initialized.                                               *
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
      }

   }  

/* last modified on Fri  1 Jul 2005 at 16:48:44 UT by lamport */
