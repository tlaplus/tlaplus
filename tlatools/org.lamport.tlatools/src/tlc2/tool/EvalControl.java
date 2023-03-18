// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, Oracle and/or its affiliates.
// Last modified on Mon 30 Apr 2007 at  9:27:06 PST by lamport 
//      modified on Fri Jan  4 22:46:57 PST 2002 by yuanyu 

package tlc2.tool;

import tlc2.util.PartialBoolean;

public class EvalControl {

  public static final int KeepLazy = 1;
  /**
   * Current evaluation within a primed variable. If isPrimed is true, lookup in
   * the Context chain terminates on a branch.
   * 
   * @see tlc2.util.Context.lookup(SymbolNode, boolean)
   */
  public static final int Primed = 1 << 1;
  /**
   * Current evaluation scope is within ENABLED. In the ENABLED scope, caching of
   * LazyValue is disabled.
   */
  public static final int Enabled = 1 << 2;
  /**
   * Evaluation in the scope of {@link ITool#getInitStates()} or
   * {@link ITool#getInitStates(IStateFunctor)}. In other words, set during the
   * generation of initial states.
   */
  public static final int Init = 1 << 3;
	/**
	 * Evaluation in the scope of {@link ITool#checkAssumptions() or
	 * {@link Worker#doPostConditionCheck}. In other words, set during the
	 * evaluation of ASSUME/ASSUMPTIONS or POSTCONDITION.
	 */
	public static final int Const = 1 << 4;
  
  public static final int Clear = 0;
  
  private static boolean isSet(final int control, final int constant) {
	  // Zero all bits except constant bit(s).
	  return (control & constant) > 0;
  }
  
  public static boolean isKeepLazy(int control) {
    return isSet(control, KeepLazy);
  }

  public static int setKeepLazy(int control) {
    return control | KeepLazy;
  }

  public static boolean isPrimed(int control) {
    return isSet(control, Primed);
  }
    
  public static int setPrimed(int control) {
    return control | Primed;
  }
    
  /**
   * Sets {@link EvalControl#Primed} iff {@link EvalControl#Enabled} is already set.
   */
  public static int setPrimedIfEnabled(int control) {
	  if (isEnabled(control)) {
		  return setPrimed(control);
	  }
	  return control;
  }
  
  public static boolean isEnabled(int control) {
    return isSet(control, Enabled);
  }

  public static int setEnabled(int control) {
	return  control | Enabled;
  }

  public static boolean isInit(int control) {
	return isSet(control, Init);
  }
	
	public static boolean isConst(int control) {
		return isSet(control, Const);
	}

    /**
     * Determine whether two {@link EvalControl} settings are semantically equivalent.  Formally,
     * they are semantically equivalent if
     * <pre>
     *     \A expr, context, behavior:
     *         eval(expr, context, behavior, control1) =
     *         eval(expr, context, behavior, control2)
     * </pre>
     *
     * <p>Many control settings like {@link #Clear} and {@link #Enabled} are not equivalent; they
     * will often result in different computed values.
     *
     * <p>This function always returns {@link PartialBoolean#YES} when
     * <code>control1 == control2</code>, and it can identify a small set of other cases where
     * the inputs are semantically equivalent.
     *
     * @param control1 the first control value
     * @param control2 the second control value
     * @return whether the values are semantically equivalent
     */
    public static PartialBoolean semanticallyEquivalent(int control1, int control2) {
        // *** CAUTION ***
        // The implementation of this function is quite subtle.  First we'll define `flagsThatCanBeSafelyIgnored`
        // as a special whitelist of flags we know won't affect the evaluation outcome.  Each whitelisted flag
        // has to be carefully justified:
        //   - KeepLazy: this is a performance hint that affects handling of function definitions.  Although it
        //     can change the exact structure of the IValue returned by eval(...), it does not affect the semantic
        //     meaning of that value.
        //   - Init: this is a flag to indicate that we are evaluating part of a specification's initial condition.
        //     It is used for debugging.
        //   - Const: similar to Init, this is a flag to indicate that we are evaluating part of a specification's
        //     constant definitions.  It is used for debugging.
        int flagsThatCanBeSafelyIgnored = KeepLazy | Init | Const;

        // Compute a mask capturing all possible flags that CAN'T be safely ignored.
        int mask = ~flagsThatCanBeSafelyIgnored;

        // If the two inputs are identical on all flags not present in `flagsThatCanBeSafelyIgnored`, then they are
        // certainly equivalent.  Otherwise, conservatively return `MAYBE`.
        return (control1 & mask) == (control2 & mask) ? PartialBoolean.YES : PartialBoolean.MAYBE;
    }
}
