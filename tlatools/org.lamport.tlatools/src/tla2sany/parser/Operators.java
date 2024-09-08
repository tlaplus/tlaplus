// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

package tla2sany.parser;

import util.UniqueString;

import java.util.Enumeration;
import java.util.Hashtable;

/**
 * Holds information about the precedence, associativity, and synonyms of all
 * TLA+ operator symbols.
 */
public class Operators {

  /**
   * The operator has no defined associativity. This is the case for prefix
   * and postfix operators.
   */
  public static final int assocNone = 0;
  
  /**
   * The operator is left-associative, like ((1 + 2) + 3).
   */
  public static final int assocLeft = 1;
  
  /**
   * The operator is right-associative, like (1 + (2 + 3)).
   * Currently, no TLA+ operators are right-associative.
   */
  public static final int assocRight = 2;

  /**
   * The operator has no -fix information associated with it.
   * It is unknown what type of operator this could refer to.
   */
  public static final int nofix = 0;
  
  /**
   * Indicates a prefix operator, like SUBSET S.
   */
  public static final int prefix = 1;
  
  /**
   * Indicates a postfix operator, like x'.
   */
  public static final int postfix = 2;
  
  /**
   * Indicates an infix operator, like 1 + 2.
   */
  public static final int infix = 3;
  
  /**
   * Indicates an n-fix operator, currently only A \X B \X C \X D.
   */
  public static final int nfix = 4;
  
  /**
   * The table holding the data for all operators defined in the language.
   */
  private static final Hashtable<UniqueString, Operator> DefinitionTable =
      new Hashtable<UniqueString, Operator>();
  
  /**
   * Gets the operator with the given name.
   * 
   * @param name The operator name.
   * @return Details about the requested operator.
   */
  public static Operator getOperator(UniqueString name) {
    return DefinitionTable.get(name);
  }

  /**
   * Converts an operator into its mixfix form. This is really only
   * applicable when turning the "-" negative prefix operator into its "-."
   * symbol-reference form.
   * 
   * @param op The operator to convert.
   * @return The mixfix form of the given operator.
   */
  public static Operator getMixfix(Operator op) {
     if (op.isPrefix()) return op;
     else {
       UniqueString id = op.getIdentifier().concat(".");
       return DefinitionTable.get(id);
     }
  }
  
  /**
   * Check whether the given operator is defined.
   * 
   * @param name The name of the operator to check for existence.
   * @return Whether the operator exists.
   */
  public static boolean existsOperator(UniqueString name) {
    return DefinitionTable.containsKey(name);
  }

  /*************************************************************************
  * resolveSynonym has the property that                                   *
  *                                                                        *
  *    resolveSynonym(a) = resolveSynonym(b)                               *
  *                                                                        *
  * iff either a = b or a and b are synonyms (like (+) and \oplus).  If a  *
  * has no synonyms, then resolveSynonym(a) = a.                           *
  *                                                                        *
  * @param name Name of the synonym to resolve.                            *
  * @return Name of the synonym to resolve.                                *
  *************************************************************************/
  public static UniqueString resolveSynonym(UniqueString name) {
    Operator op = DefinitionTable.get(name);
    return null == op ? name : op.getIdentifier();
  }

  /**
   * Useful for debugging purposes.
   */
  public static void printTable() {
    System.out.println("printing Operators table");
    Enumeration<UniqueString> Enum = DefinitionTable.keys();
    while( Enum.hasMoreElements() ) { System.out.println("-> " + ((UniqueString)Enum.nextElement()).toString() ); }
  }

  /**
   * Canonical operators & symbols with their defining characteristics:
   * symbol text, low precedence, high precedence, associativity, fix type.
   */
  private static final Operator[] CanonicalOperators = {
    new Operator("[",             160, 160, Operators.assocLeft, Operators.postfix),
    new Operator(".",             170, 170, Operators.assocLeft, Operators.infix),
    new Operator("'",             150, 150, Operators.assocNone, Operators.postfix),
    new Operator("^",             140, 140, Operators.assocNone, Operators.infix),
    new Operator("/",             130, 130, Operators.assocNone, Operators.infix),
    new Operator("*",             130, 130, Operators.assocLeft, Operators.infix),
    new Operator("-",             110, 110, Operators.assocLeft, Operators.infix),
    new Operator("-.",            120, 120, Operators.assocNone, Operators.prefix),
    new Operator("+",             100, 100, Operators.assocLeft, Operators.infix),
    new Operator("=",             50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\lnot",        40,  40,  Operators.assocLeft, Operators.prefix),
    new Operator("\\land",        30,  30,  Operators.assocLeft, Operators.infix),
    new Operator("\\lor",         30,  30,  Operators.assocLeft, Operators.infix),
    new Operator("~>",            20,  20,  Operators.assocNone, Operators.infix),
    new Operator("=>",            10,  10,  Operators.assocNone, Operators.infix),
    new Operator("[]",            40,  150, Operators.assocNone, Operators.prefix),
    new Operator("<>",            40,  150, Operators.assocNone, Operators.prefix),
    new Operator("ENABLED",       40,  150, Operators.assocNone, Operators.prefix),
    new Operator("UNCHANGED",     40,  150, Operators.assocNone, Operators.prefix),
    new Operator("SUBSET",        100, 130, Operators.assocNone, Operators.prefix),
    new Operator("UNION",         100, 130, Operators.assocNone, Operators.prefix),
    new Operator("DOMAIN",        100, 130, Operators.assocNone, Operators.prefix),
    new Operator("^+",            150, 150, Operators.assocNone, Operators.postfix),
    new Operator("^*",            150, 150, Operators.assocNone, Operators.postfix),
    new Operator("^#",            150, 150, Operators.assocNone, Operators.postfix),
    new Operator("\\cdot",        50,  140, Operators.assocLeft, Operators.infix),
    new Operator("\\equiv",       20,  20,  Operators.assocNone, Operators.infix),
    new Operator("-+->",          20,  20,  Operators.assocNone, Operators.infix),
    new Operator("/=",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\subseteq",    50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\in",          50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\notin",       50,  50,  Operators.assocNone, Operators.infix),
    new Operator("<",             50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\leq",         50,  50,  Operators.assocNone, Operators.infix),
    new Operator(">",             50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\geq",         50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\times",       100, 130, Operators.assocLeft, Operators.nfix),
    new Operator("\\",            80,  80,  Operators.assocNone, Operators.infix),
    new Operator("\\intersect",   80,  80,  Operators.assocLeft, Operators.infix),
    new Operator("\\union",       80,  80,  Operators.assocLeft, Operators.infix),
    new Operator("...",           90,  90,  Operators.assocNone, Operators.infix),
    new Operator("..",            90,  90,  Operators.assocNone, Operators.infix),
    new Operator("|",             100, 110, Operators.assocLeft, Operators.infix),
    new Operator("||",            100, 110, Operators.assocLeft, Operators.infix),
    new Operator("&&",            130, 130, Operators.assocLeft, Operators.infix),
    new Operator("&",             130, 130, Operators.assocLeft, Operators.infix),
    new Operator("$$",            90,  130, Operators.assocLeft, Operators.infix),
    new Operator("$",             90,  130, Operators.assocLeft, Operators.infix),
    new Operator("??",            90,  130, Operators.assocLeft, Operators.infix),
    // Removed as requested by Leslie (16 Feb. 01)
    //new Operator("?",             90,  130, Operators.assocLeft, Operators.infix),
    new Operator("%%",            100, 110, Operators.assocLeft, Operators.infix),
    new Operator("%",             100, 110, Operators.assocNone, Operators.infix),
    new Operator("##",            90,  130, Operators.assocLeft, Operators.infix),
    new Operator("++",            100, 100, Operators.assocLeft, Operators.infix),
    new Operator("--",            110, 110, Operators.assocLeft, Operators.infix),
    new Operator("**",            130, 130, Operators.assocLeft, Operators.infix),
    new Operator("//",            130, 130, Operators.assocNone, Operators.infix),
    new Operator("^^",            140, 140, Operators.assocNone, Operators.infix),
    new Operator("@@",            60,  60,  Operators.assocLeft, Operators.infix),
    new Operator("!!",            90,  130, Operators.assocNone, Operators.infix),
    new Operator("|-",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("|=",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("-|",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("=|",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("<:",            70,  70,  Operators.assocNone, Operators.infix),
    new Operator(":>",            70,  70,  Operators.assocNone, Operators.infix),
    new Operator(":=",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("::=",           50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\oplus",       100, 100, Operators.assocLeft, Operators.infix),
    new Operator("\\ominus",      110, 110, Operators.assocLeft, Operators.infix),
    new Operator("\\odot",        130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\oslash",      130, 130, Operators.assocNone, Operators.infix),
    new Operator("\\otimes",      130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\uplus",       90,  130, Operators.assocLeft, Operators.infix),
    new Operator("\\sqcap",       90,  130, Operators.assocLeft, Operators.infix),
    new Operator("\\sqcup",       90,  130, Operators.assocLeft, Operators.infix),
    new Operator("\\div",         130, 130, Operators.assocNone, Operators.infix),
    new Operator("\\wr",          90,  140, Operators.assocNone, Operators.infix),
    new Operator("\\star",        130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\o",           130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\bigcirc",     130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\bullet",      130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\prec",        50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\succ",        50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\preceq",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\succeq",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sim",         50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\simeq",       50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\ll",          50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\gg",          50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\asymp",       50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\subset",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\supset",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\supseteq",    50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\approx",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\cong",        50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sqsubset",    50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sqsubseteq",  50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sqsupset",    50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sqsupseteq",  50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\doteq",       50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\propto",      50,  50,  Operators.assocNone, Operators.infix),
  };
  
  /*
   * Different ways of writing the same operator. The zeroeth item is the
   * canonical way.
   */
  private static final String[][] OperatorSynonyms = new String[][] {
    new String[] {"\\lnot", "~", "\\neg", "¬"},
    new String[] {"[]", "□"},
    new String[] {"<>", "◇"},
    new String[] {"\\land", "/\\", "∧"},
    new String[] {"\\lor", "\\/", "∨"},
    new String[] {"\\equiv", "<=>", "≡", "⇔"},
    new String[] {"/=", "#", "≠"},
    new String[] {"\\leq", "<=", "=<", "≤"},
    new String[] {"\\geq", ">=", "≥"},
    new String[] {"\\times", "\\X", "×"},
    new String[] {"\\intersect", "\\cap", "∩"},
    new String[] {"\\union", "\\cup", "∪"},
    new String[] {"\\o", "\\circ", "∘"},
    new String[] {"\\oplus", "(+)", "⊕"},
    new String[] {"\\ominus", "(-)", "⊖"},
    new String[] {"\\odot", "(.)", "⊙"},
    new String[] {"\\oslash", "(/)", "⊘"},
    new String[] {"\\otimes", "(\\X)", "⊗"},
    new String[] {"\\approx", "≈"},
    new String[] {":=", "≔"},
    new String[] {"\\asymp", "≍"},
    new String[] {"\\bigcirc", "◯"},
    new String[] {"::=", "⩴"},
    new String[] {"\\bullet", "●"},
    new String[] {"\\cdot", "⋅"},
    new String[] {"\\cong", "≅"},
    new String[] {"\\div", "÷"},
    new String[] {"\\doteq", "≐"},
    new String[] {"..", "‥"},
    new String[] {"...", "…"},
    new String[] {"!!", "‼"},
    new String[] {"\\gg", "≫"},
    new String[] {"=>", "⇒"},
    new String[] {"\\in", "∈"},
    new String[] {"=|", "⫤"},
    new String[] {"~>", "↝"},
    new String[] {"\\ll", "≪"},
    new String[] {"-|", "⊣"},
    new String[] {"\\notin", "∉"},
    new String[] {"-+->", "⇸"},
    new String[] {"\\prec", "≺"},
    new String[] {"\\preceq", "⪯"},
    new String[] {"\\propto", "∝"},
    new String[] {"??", "⁇"},
    // This synonym was disabled in the parser so disabling it here too
    //new String[] {"%", "\mod"},
    new String[] {"|=", "⊨"},
    new String[] {"|-", "⊢"},
    new String[] {"\\sim", "∼"},
    new String[] {"\\simeq", "≃"},
    new String[] {"\\sqcap", "⊓"},
    new String[] {"\\sqcup", "⊔"},
    new String[] {"\\sqsubset", "⊏"},
    new String[] {"\\sqsubseteq", "⊑"},
    new String[] {"\\sqsupset", "⊐"},
    new String[] {"\\sqsupseteq", "⊒"},
    new String[] {"\\star", "⋆"},
    new String[] {"\\subset", "⊂"},
    new String[] {"\\subseteq", "⊆"},
    new String[] {"\\succ", "≻"},
    new String[] {"\\succeq", "⪰"},
    new String[] {"\\supset", "⊃"},
    new String[] {"\\supseteq", "⊇"},
    new String[] {"\\uplus", "⊎"},
    new String[] {"||", "‖"},
    new String[] {"\\wr", "≀"},
    new String[] {"^+", "⁺"},
  };

  /**
   * Statically initializes all operators in the definition table. This will
   * be executed when this class loads into memory.
   */
  static {
    for (Operator op : CanonicalOperators) {
      DefinitionTable.put(op.getIdentifier(), op);
    }
    
    for (String[] synonyms : OperatorSynonyms) {
      UniqueString canonical = UniqueString.uniqueStringOf(synonyms[0]);
      Operator canonicalOp = DefinitionTable.get(canonical);
      if (null == canonicalOp) {
        throw new RuntimeException(
            "Error during static initialization of definitions "
            + "table: attempted to add synonym for nonexistent "
            + "canonical operator " + canonical.toString());
      }
      for (int i = 1; i < synonyms.length; i++) {
        UniqueString synonym = UniqueString.uniqueStringOf(synonyms[i]);
        DefinitionTable.put(synonym, canonicalOp);
      }
    }
  }
}
