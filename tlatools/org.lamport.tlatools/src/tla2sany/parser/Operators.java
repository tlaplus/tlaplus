package tla2sany.parser;

import tla2sany.configuration.ConfigConstants;
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
  static public final int assocNone = 0;
  
  /**
   * The operator is left-associative, like ((1 + 2) + 3).
   */
  static public final int assocLeft = 1;
  
  /**
   * The operator is right-associative, like (1 + (2 + 3)).
   * Currently, no TLA+ operators are right-associative.
   */
  static public final int assocRight = 2;

  /**
   * The operator has no -fix information associated with it.
   * It is unknown what type of operator this could refer to.
   */
  static public final int nofix = 0;
  
  /**
   * Indicates a prefix operator, like SUBSET S.
   */
  static public final int prefix = 1;
  
  /**
   * Indicates a postfix operator, like x'.
   */
  static public final int postfix = 2;
  
  /**
   * Indicates an infix operator, like 1 + 2.
   */
  static public final int infix = 3;
  
  /**
   * Indicates an n-fix operator, currently only A \X B \X C \X D.
   */
  static public final int nfix = 4;
  
  /**
   * The table holding the data for all operators defined in the language.
   */
  static private final Hashtable<UniqueString, Operator> DefinitionTable =
      new Hashtable<UniqueString, Operator>();
  
  /**
   * Statically initializes all operators in the definition table. This will
   * be executed when this class loads into memory.
   */
  static {
    for (Operator op : ConfigConstants.CanonicalOperators) {
      DefinitionTable.put(op.getIdentifier(), op);
    }
    
    for (String[] synonyms : ConfigConstants.OperatorSynonyms) {
      UniqueString canonical = UniqueString.uniqueStringOf(synonyms[0]);
      Operator canonicalOp = DefinitionTable.get(canonical);
      if (null == canonicalOp) {
        throw new IllegalArgumentException(
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

  /**
   * Gets the operator with the given name.
   * 
   * @param name The operator name.
   * @return Details about the requested operator.
   */
  static public Operator getOperator(UniqueString name) {
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
  static public Operator getMixfix(Operator op) {
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
  static public boolean existsOperator(UniqueString name) {
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
  static public UniqueString resolveSynonym(UniqueString name) {
    Operator op = DefinitionTable.get(name);
    return null == op ? name : op.getIdentifier();
  }

  /**
   * Useful for debugging purposes.
   */
  static public void printTable() {
    System.out.println("printing Operators table");
    Enumeration<UniqueString> Enum = DefinitionTable.keys();
    while( Enum.hasMoreElements() ) { System.out.println("-> " + ((UniqueString)Enum.nextElement()).toString() ); }
  }
}
