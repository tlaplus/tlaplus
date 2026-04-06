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
     * The level of the operator.
     */
    public final int OpLevel;

    /**
     * The maximum level of the operator's parameters.
     */
    public final int[] ArgMaxLevels;

    /**
     * The weights of the operator's parameters.
     */
    public final int[] ArgWeights;

    /**
     * Constructs a new instance of the BuiltInOperator class.
     * 
     * @param name The operator's name.
     * @param arity The operator's arity.
     * @param opLevel The operator's level.
     * @param argMaxLevels The max levels of the operator's parameters.
     * @param argWeights The weights of the operator's parameters.
     */
    public BuiltInOperator(
      String name,
      int arity,
      int opLevel,
      int[] argMaxLevels,
      int[] argWeights
    ) {
      this.Name = UniqueString.uniqueStringOf(name);
      this.Arity = arity;
      this.OpLevel = opLevel;
      this.ArgMaxLevels = argMaxLevels;
      this.ArgWeights = argWeights;
    }
  }
  
  /**
   * Quick helper function to construct an array.
   *
   * @param vals The values to put into the array.
   * @return An array of the given values.
   */
  private static int[] mk(int... vals) {
    return vals;
  }

  /**
   * A list of all built-in operators along with their arities and levels.
   */
  public static final BuiltInOperator[] Properties = {
    new BuiltInOperator("STRING",               0,  0,  mk(),       mk()),
    new BuiltInOperator("FALSE",                0,  0,  mk(),       mk()),
    new BuiltInOperator("TRUE",                 0,  0,  mk(),       mk()),
    new BuiltInOperator("BOOLEAN",              0,  0,  mk(),       mk()),
    new BuiltInOperator("=",                    2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("/=",                   2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("'",                    1,  2,  mk(1),      mk(0)),
    new BuiltInOperator("\\lnot",               1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("\\land",               2,  0,  mk(3,3),    mk(1,1)),
    new BuiltInOperator("\\lor",                2,  0,  mk(3,3),    mk(1,1)),
    new BuiltInOperator("\\equiv",              2,  0,  mk(3,3),    mk(1,1)),
    new BuiltInOperator("=>",                   2,  0,  mk(3,3),    mk(1,1)),
    new BuiltInOperator("SUBSET",               1,  0,  mk(2),      mk(1)),
    new BuiltInOperator("UNION",                1,  0,  mk(2),      mk(1)),
    new BuiltInOperator("DOMAIN",               1,  0,  mk(2),      mk(1)),
    new BuiltInOperator("\\subseteq",           2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("\\in",                 2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("\\notin",              2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("\\",                   2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("\\intersect",          2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("\\union",              2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("~>",                   2,  3,  mk(3,3),    mk(0,0)),
    new BuiltInOperator("[]",                   1,  3,  mk(3),      mk(0)),
    new BuiltInOperator("<>",                   1,  3,  mk(3),      mk(0)),
    new BuiltInOperator("ENABLED",              1,  1,  mk(2),      mk(0)),
    new BuiltInOperator("UNCHANGED",            1,  2,  mk(1),      mk(0)),
    new BuiltInOperator("\\cdot",               2,  2,  mk(2,2),    mk(0,0)),
    new BuiltInOperator("-+->",                 2,  3,  mk(3,3),    mk(0,0)),
    new BuiltInOperator("$AngleAct",            2,  2,  mk(2,1),    mk(0,0)),
    new BuiltInOperator("$BoundedChoose",       -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$BoundedExists",       -1, 0,  mk(3),      mk(1)),
    new BuiltInOperator("$BoundedForall",       -1, 0,  mk(3),      mk(1)),
    new BuiltInOperator("$CartesianProd",       -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$Case",                -1, 0,  mk(3),      mk(1)),
    new BuiltInOperator("$ConjList",            -1, 0,  mk(3),      mk(1)),
    new BuiltInOperator("$DisjList",            -1, 0,  mk(3),      mk(1)),
    new BuiltInOperator("$Except",              -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$FcnApply",            2,  0,  mk(2,2),    mk(1,1)),
    new BuiltInOperator("$FcnConstructor",      -1, 0,  mk(3),      mk(1)),
    new BuiltInOperator("$IfThenElse",          3,  0,  mk(3,3,3),  mk(1,1,1)),
    new BuiltInOperator("$NonRecursiveFcnSpec", 1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$Pair",                2,  0,  mk(3,3),    mk(1,1)),
    new BuiltInOperator("$RcdConstructor",      -1, 0,  mk(3),      mk(1)),
    new BuiltInOperator("$RcdSelect",           2,  0,  mk(2,0),    mk(1,1)),
    new BuiltInOperator("$RecursiveFcnSpec",    1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$Seq",                 -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$SetEnumerate",        -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$SetOfAll",            -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$SetOfFcns",           -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$SetOfRcds",           -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$SF",                  2,  3,  mk(1,2),    mk(0,0)),
    new BuiltInOperator("$SquareAct",           2,  2,  mk(2,1),    mk(0,0)),
    new BuiltInOperator("$SubsetOf",            1,  0,  mk(2),      mk(1)),
    new BuiltInOperator("$TemporalExists",      1,  3,  mk(3),      mk(0)),
    new BuiltInOperator("$TemporalForall",      1,  3,  mk(3),      mk(0)),
    new BuiltInOperator("$Tuple",               -1, 0,  mk(2),      mk(1)),
    new BuiltInOperator("$UnboundedChoose",     1,  0,  mk(2),      mk(1)),
    new BuiltInOperator("$UnboundedExists",     1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$UnboundedForall",     1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$WF",                  2,  3,  mk(1,2),    mk(0,0)),
    new BuiltInOperator("$Nop",                 1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$Qed",                 0,  0,  mk(),       mk()),
    new BuiltInOperator("$Pfcase",              1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$Have",                1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$Take",                1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$Pick",                1,  0,  mk(3),      mk(1)),
    new BuiltInOperator("$Witness",             -1,  0, mk(2),      mk(1)),
    new BuiltInOperator("$Suffices",            1,  0,  mk(3),      mk(1)),
  };
}