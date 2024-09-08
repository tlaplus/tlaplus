package tla2sany.semantic;

import util.UniqueString;

/**
 * Operators that have built-in implementations in the TLA+ interpreter.
 * Users do not need to import modules to access these operators, and users
 * cannot redefine these operators.
 */
public class BuiltInOperators {

  /**
   * Various parameters that must be set for a built-in operator.
   */
  public static class BuiltInOperator {
    
    /**
     * The operator's name, usually its string representation in source
     * files if such a thing exists.
     */
    public final UniqueString Name;
    
    /**
     * Number of parameters the operator accepts.
     */
    public final int Arity;
    
    /**
     * Constructs a new instance of the BuiltInOperator class.
     * 
     * @param name The operator's name.
     * @param arity The operator's arity.
     */
    public BuiltInOperator(
      String name,
      int arity
    ) {
      this.Name = UniqueString.uniqueStringOf(name);
      this.Arity = arity;
    }
  }
  
  /**
   * A list of all built-in operators and their arities.
   */
  public static final BuiltInOperator[] Properties = {
    new BuiltInOperator("STRING",               0),
    new BuiltInOperator("FALSE",                0),
    new BuiltInOperator("TRUE",                 0),
    new BuiltInOperator("BOOLEAN",              0),
    new BuiltInOperator("=",                    2),
    new BuiltInOperator("/=",                   2),
    new BuiltInOperator(".",                    2),
    new BuiltInOperator("'",                    1),
    new BuiltInOperator("\\lnot",               1),
    new BuiltInOperator("\\neg",                1),
    new BuiltInOperator("\\land",               2),
    new BuiltInOperator("\\lor",                2),
    new BuiltInOperator("\\equiv",              2),
    new BuiltInOperator("=>",                   2),
    new BuiltInOperator("SUBSET",               1),
    new BuiltInOperator("UNION",                1),
    new BuiltInOperator("DOMAIN",               1),
    new BuiltInOperator("\\subseteq",           2),
    new BuiltInOperator("\\in",                 2),
    new BuiltInOperator("\\notin",              2),
    new BuiltInOperator("\\",                   2),
    new BuiltInOperator("\\intersect",          2),
    new BuiltInOperator("\\union",              2),
    new BuiltInOperator("\\times",              2),
    new BuiltInOperator("~>",                   2),
    new BuiltInOperator("[]",                   1),
    new BuiltInOperator("<>",                   1),
    new BuiltInOperator("ENABLED",              1),
    new BuiltInOperator("UNCHANGED",            1),
    new BuiltInOperator("\\cdot",               2),
    new BuiltInOperator("-+->",                 2),
    new BuiltInOperator("$AngleAct",            2),
    new BuiltInOperator("$BoundedChoose",       -1),
    new BuiltInOperator("$BoundedExists",       -1),
    new BuiltInOperator("$BoundedForall",       -1),
    new BuiltInOperator("$CartesianProd",       -1),
    new BuiltInOperator("$Case",                -1),
    new BuiltInOperator("$ConjList",            -1),
    new BuiltInOperator("$DisjList",            -1),
    new BuiltInOperator("$Except",              -1),
    new BuiltInOperator("$FcnApply",            2),
    new BuiltInOperator("$FcnConstructor",      -1),
    new BuiltInOperator("$IfThenElse",          3),
    new BuiltInOperator("$NonRecursiveFcnSpec", 1),
    new BuiltInOperator("$Pair",                2),
    new BuiltInOperator("$RcdConstructor",      -1),
    new BuiltInOperator("$RcdSelect",           2),
    new BuiltInOperator("$RecursiveFcnSpec",    1),
    new BuiltInOperator("$Seq",                 -1),
    new BuiltInOperator("$SetEnumerate",        -1),
    new BuiltInOperator("$SetOfAll",            -1),
    new BuiltInOperator("$SetOfFcns",           -1),
    new BuiltInOperator("$SetOfRcds",           -1),
    new BuiltInOperator("$SF",                  2),
    new BuiltInOperator("$SquareAct",           2),
    new BuiltInOperator("$SubsetOf",            1),
    new BuiltInOperator("$TemporalExists",      1),
    new BuiltInOperator("$TemporalForall",      1),
    new BuiltInOperator("$TemporalWhile",       2),
    new BuiltInOperator("$Tuple",               -1),
    new BuiltInOperator("$UnboundedChoose",     1),
    new BuiltInOperator("$UnboundedExists",     1),
    new BuiltInOperator("$UnboundedForall",     1),
    new BuiltInOperator("$WF",                  2),
    new BuiltInOperator("$Nop",                 1),
    new BuiltInOperator("$Qed",                 0),
    new BuiltInOperator("$Pfcase",              1),
    new BuiltInOperator("$Have",                1),
    new BuiltInOperator("$Take",                1),
    new BuiltInOperator("$Pick",                1),
    new BuiltInOperator("$Witness",             -1),
    new BuiltInOperator("$Suffices",            1)
  };
}