// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, 2025, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 15:30:08 PST by lamport
//      modified on Thu Feb  8 21:23:55 PST 2001 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import util.ToolIO;

/**
 * LazyValue is TLA+ expression that has not been reduced to a simple value.  It might also be called a
 * <a href="https://en.wikipedia.org/wiki/Thunk">"thunk"</a>.  LazyValues enable TLC's lazy
 * <a href="https://en.wikipedia.org/wiki/Evaluation_strategy#Call_by_need">call-by-need</a> evaluation order.
 *
 * <h2>The Need for Laziness</h2>
 *
 * <p>TLC uses LazyValue when it "computes" the arguments to an operator or the bound value in a LET...IN expression.
 * Because TLA+ has temporal operators, it cannot behave like a normal call-by-value interpreter in these cases.
 *
 * <p>For example, suppose a TLA+ spec contains the definition
 * <pre>
 *     F(x) == x'
 * </pre>
 * and TLC has to evaluate the expression <code>F(var)</code> in a behavior where <code>var = 1</code> and
 * <code>var' = 2</code>.  The correct output is 2.  However, fully reducing the argument <code>var</code> before
 * expanding <code>F</code> would lead to wrong output:
 * <pre>
 *     F(var) = F(1)   \* wrong!
 *            = 1'
 *            = 1
 *
 *     F(var) = var'   \* right!
 *            = 2
 * </pre>
 * When expanding <code>F</code> TLC needs to keep the expression that was used as the <code>x</code> argument in order
 * to get the right output.
 *
 * <h2>Caching and Performance</h2>
 *
 * <p>For performance, LazyValue can cache the reduced value when it is computed.  This enables TLC to have similar
 * performance to a call-by-value language in many cases.  For example, if <code>G(x) == x + x</code>, then evaluating
 * the expression <code>G(very_expensive_arg)</code> should only evaluate the very expensive argument once.
 *
 * <p>TLC has had multiple soundness bugs due to mishandling of cached LazyValues: see Github issues #113 and #798.  As
 * a result, reads of the cached value are now guarded and callers must specify the tool, behavior, and evaluation mode
 * they are using when reading it (see {@link #getCachedValue(Tool, TLCState, TLCState, int)}).
 *
 * <p>The performance benefits of caching values is generally debatable. The time
 * it takes TLC to check a reasonable sized model of the PaxosCommit [1] spec is
 * ~2h with, with limited caching due to the fix for issue 113 or without
 * caching. There is no measurable performance difference even though the change
 * for issue 113 reduces the cache hits from ~13 billion to ~4 billion. This was
 * measured with an instrumented version of TLC.
 * [1] general/performance/PaxosCommit/
 *
 * @see #getValue(Tool, TLCState, TLCState, int)
 */
public class LazyValue {
	/**
	 * Allow to completely disable LazyValue by passing a VM property/system
	 * property to the Java VM with "-Dtlc2.value.LazyValue.off=true". This is meant
	 * for debug purposes only and can be removed at any time. This is not API.
	 * 
	 * This property was added 01/12/2018 by Markus Kuppe in the process of fixing a
	 * bug where TLC generates and incorrect set of states with certain statements.
	 * More details can be found at https://github.com/tlaplus/tlaplus/issues/113.
	 */
	public static final boolean LAZYEVAL_OFF = Boolean.getBoolean(tlc2.value.impl.LazyValue.class.getName() + ".off");
	
	static {
		// Indicate if LazyValue will be disabled in this TLC run.
		if (LAZYEVAL_OFF) {
			ToolIO.out.println("LazyValue is disabled.");
		}
	}

  public final SemanticNode expr;
  public final Context con;

  /**
   * The field val is the result of evaluating expr in context con and
   * a pair of states.  If val is null, then the value has not been
   * computed, but when computed, the value can be cached in the field
   * val. If val is ValUndef, then the value has not been computed,
   * and when computed, it can not be cached in the field val.
   */
  private Value val;
  private int toolID;
  private TLCState s0;
  private TLCState s1;
  private int control;
  private int cacheCount = 0;
  public final CostModel cm; // TODO: either make this field private or inline+remove getCostModel()

  public LazyValue(SemanticNode expr, Context con, final CostModel cm) {
	  this(expr, con, true, Value.coverage ? cm.get(expr) : cm);
  }

  public LazyValue(SemanticNode expr, Context con, final boolean cachable, final CostModel cm) {
    this.expr = expr;
    this.con = con;
    this.cm = Value.coverage ? cm.get(expr) : cm;
    this.val = null;
    // See comment on cachable's meager performance in the docstring above.
    // See other note about a bug that surfaced with LazyValue in the docstring above.
    if (LAZYEVAL_OFF || !cachable) {
    	this.val = UndefValue.ValUndef;
    }
  }

  public CostModel getCostModel() {
    return cm;
  }

  private boolean isCachable() { return this.val != UndefValue.ValUndef; }

  /** For testing only. */
  public int getNumTimesThatANewValueWasCached() {
    return cacheCount;
  }

  /**
   * Equivalent to {@link #getValue(Tool, TLCState, TLCState, int)}, but does not
   * compute a new value.  Instead, if a new value would need to be computed, this
   * method returns null.
   *
   * @param tool a tool that evaluates expressions
   * @param s0 the first state in the behavior
   * @param s1 the next state in the behavior
   * @param control see {@link EvalControl}
   * @return a cached value for the given tool, behavior, and control; or null if
   *         computing the requested value would require work
   */
  public Value getCachedValue(Tool tool, TLCState s0, TLCState s1, int control) {
    if (val != null &&
            isCachable() &&
            tool.getId() == toolID &&
            TLCState.isSubset(s0, this.s0).isDefinitely(true) &&
            TLCState.isSubset(s1, this.s1).isDefinitely(true) &&
            EvalControl.semanticallyEquivalent(control, this.control).isDefinitely(true)) {
      return val;
    }
    return null;
  }

  /**
   * Reduce this LazyValue to a fully-reduced value in the given behavior.
   * The returned value might be cached to accelerate future calls.  LazyValue
   * guarantees not to misuse the cached value; if this method is called later
   * with a different tool, behavior, or control option that is incompatible
   * with the ones used to compute the cached value, then the cached value will
   * not be returned.
   *
   * @param tool a tool that evaluates expressions
   * @param s0 the first state in the behavior
   * @param s1 the next state in the behavior
   * @param control see {@link EvalControl}
   * @return a fully-reduced value
   */
  public Value getValue(Tool tool, TLCState s0, TLCState s1, int control) {
    Value res = getCachedValue(tool, s0, s1, control);
    if (res == null) {
      res = tool.eval(this.expr, this.con, s0, s1, control, getCostModel());
      if (isCachable()) {
        this.val = res;
        this.toolID = tool.getId();
        this.s0 = s0 != null ? s0.copy() : null;
        this.s1 = s1 != null ? s1.copy() : null;
        this.control = control;
        ++cacheCount;
      }
    }
    return res;
  }

  /* The string representation of the value. */
  @Override
  public String toString() {
    if (this.val == null || this.val == UndefValue.ValUndef) {
      return "<LAZY " + this.expr + '>';
    }
    return this.val.toString();
  }

  public IValue eval(Tool tool) {
		return eval(tool, TLCState.Empty);
	}

  public IValue eval(Tool tool, TLCState s0) {
		return eval(tool, s0, null);
	}

  public IValue eval(Tool tool, TLCState s0, TLCState s1) {
		final Value eval = tool.eval(expr, con, s0, s1, EvalControl.Clear, cm);
		if (!eval.hasSource()) {
			// See comment at tlc2.debug.TLCStackFrame.getVariable(IValue, SymbolNode)
			eval.setSource(this.expr);
		}
		return eval;
	}
}
