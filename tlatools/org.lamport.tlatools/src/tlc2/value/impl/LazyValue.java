// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 15:30:08 PST by lamport
//      modified on Thu Feb  8 21:23:55 PST 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.FingerprintException;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import util.Assert;
import util.ToolIO;

/**
 * LazyValue is TLA+ expression that has not been reduced to a simple value.
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
public class LazyValue extends Value {
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
   * The value of expr in context con, and the tool, states, and control
   * with which TLC evaluated it. Workers may share a lazy value, so a worker
   * replaces the whole entry and never changes one of its fields.
   */
  private static final class Cache {
    private final Value val;
    private final int toolID;
    private final TLCState s0;
    private final TLCState s1;
    private final int control;

    private Cache(final Value val, final int toolID, final TLCState s0, final TLCState s1, final int control) {
      this.val = val;
      this.toolID = toolID;
      this.s0 = s0;
      this.s1 = s1;
      this.control = control;
    }
  }

  private static final Cache UNCACHABLE = new Cache(UndefValue.ValUndef, 0, null, null, 0);

  /**
   * If cache is null, then the value has not been computed, but when
   * computed, the value can be cached. If cache is UNCACHABLE, then the
   * value has not been computed, and when computed, it can not be cached.
   * A method must read cache only once.
   */
  private volatile Cache cache;
  private int cacheCount = 0;

  public LazyValue(SemanticNode expr, Context con, final CostModel cm) {
	  this(expr, con, true, coverage ? cm.get(expr) : cm);
  }

  public LazyValue(SemanticNode expr, Context con, final boolean cachable, final CostModel cm) {
    this.expr = expr;
    this.con = con;
    this.cm = coverage ? cm.get(expr) : cm;
    this.cache = null;
    // See comment on cachable's meager performance in the docstring above.
    // See other note about a bug that surfaced with LazyValue in the docstring above.
    if (LAZYEVAL_OFF || !cachable) {
    	this.cache = UNCACHABLE;
    }
  }

  private Value val() {
    final Cache cache = this.cache;
    return cache == null ? null : cache.val;
  }

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
    final Cache cache = this.cache;
    if (cache != null &&
            cache != UNCACHABLE &&
            tool.getId() == cache.toolID &&
            TLCState.isSubset(s0, cache.s0).isDefinitely(true) &&
            TLCState.isSubset(s1, cache.s1).isDefinitely(true) &&
            EvalControl.semanticallyEquivalent(control, cache.control).isDefinitely(true)) {
      return cache.val;
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
      if (this.cache != UNCACHABLE) {
        // Workers that race here each publish a whole entry, and whichever entry
        // stays, getCachedValue returns its value only for its states.
        this.cache = new Cache(res, tool.getId(), s0 != null ? s0.copy() : null,
            s1 != null ? s1.copy() : null, control);
        ++cacheCount;
      }
    }
    return res;
  }

  @Override
  public final byte getKind() { return LAZYVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to compare lazy values.", getSource());
      }
      return val.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to check equality of lazy values.", getSource());
      }
      return val.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean member(Value elem) {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to check set membership of lazy values.", getSource());
      }
      return val.member(elem);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to check if a lazy value is a finite set.", getSource());
      }
      return val.isFinite();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept ex) {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to apply EXCEPT construct to lazy value.", getSource());
      }
      return val.takeExcept(ex);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept[] exs) {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to apply EXCEPT construct to lazy value.", getSource());
      }
      return val.takeExcept(exs);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final int size() {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
         Assert.fail("Error(TLC): Attempted to compute size of lazy value.", getSource());
      }
      return val.size();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private void readObject(ObjectInputStream ois) throws IOException, ClassNotFoundException {
    this.cache = new Cache((Value)ois.readObject(), 0, null, null, 0);
  }

  private void writeObject(ObjectOutputStream oos) throws IOException {
    final Value val = this.val();
    if (val == null || val == UndefValue.ValUndef) {
      Assert.fail("Error(TLC): Attempted to serialize lazy value.", getSource());
    }
    oos.writeObject(val);
  }

  /* Nothing to normalize. */
  @Override
  public final boolean isNormalized() {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to normalize lazy value.", getSource());
      }
      return val.isNormalized();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value normalize() {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to normalize lazy value.", getSource());
      }
      val.normalize();
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isDefined() { return true; }

  @Override
  public final IValue deepCopy() {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) return this;
      return val.deepCopy();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The fingerprint method */
  @Override
  public final long fingerPrint(long fp) {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to fingerprint a lazy value.", getSource());
      }
      return val.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        Assert.fail("Error(TLC): Attempted to apply permutation to lazy value.", getSource());
      }
      return val.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The string representation of the value. */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      final Value val = this.val();
      if (val == null || val == UndefValue.ValUndef) {
        return sb.append("<LAZY " + this.expr + ">");
      }
      return val.toString(sb, offset, swallow);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
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
