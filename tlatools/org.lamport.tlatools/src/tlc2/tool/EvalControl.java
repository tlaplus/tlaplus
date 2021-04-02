// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:27:06 PST by lamport 
//      modified on Fri Jan  4 22:46:57 PST 2002 by yuanyu 

package tlc2.tool;

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
}
