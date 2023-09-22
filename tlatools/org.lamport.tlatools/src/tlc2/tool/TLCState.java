// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, Oracle and/or its affiliates.
// Last modified on Mon 30 Apr 2007 at 15:29:58 PST by lamport
//      modified on Tue Oct 23 16:48:38 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.Callable;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SymbolNode;
import tlc2.output.EC;
import tlc2.util.PartialBoolean;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.impl.Value;
import util.Assert;
import util.UniqueString;

public abstract class TLCState implements Cloneable, Serializable {
  public short workerId = Short.MAX_VALUE; // Must be set to a non-negative number. Valid worker ids \in [0,Short.MAX_VALUE] and start at 0.
  public static final int INIT_UID = -1;
  public long uid = INIT_UID;   // Must be set to a non-negative number
  // The level of an initial state is initialized with 1 to assert that
  // TLCGet("level") in the first evaluation of the next-state relation equals 1.
  // The successor states of initial states have level 2.  During the evaluation
  // of the initial *predicate* - which generates the initial states - the level
  // is defined to be zero.
  public static final int INIT_LEVEL = 1;
  private int level = INIT_LEVEL;
  
  // Set by subclasses. Cannot set until we know what the variables are.
  public static final TLCState Null = null;
  public static TLCState Empty = null;

  public static boolean isEmpty(final TLCState state) {
	  return Empty == state;
  }
  
  // The state variables.
  protected static OpDeclNode[] vars = null;

  public void read(IValueInputStream vis) throws IOException {
	this.workerId = vis.readShortNat();
	this.uid = vis.readLongNat();
    this.level = vis.readShortNat();
    assert this.level >= 0; // Should never overflow.
  }
  
	public void write(IValueOutputStream vos) throws IOException {
		if (this.level > Short.MAX_VALUE) {
			// The on-disk representation of TLCState limits the diameter/level to
			// Short.MAX_VALUE whereas the in-memory rep supports int. The underlying
			// assumption being that state spaces with a diameter beyond 32767 AND which
			// require TLC to swap the state queue to disk are infeasible to check anyway.
			// However, one can easily come up with a spec that corresponds to few, very long
			// behaviors which can be kept in memory.
			Assert.fail(EC.TLC_TRACE_TOO_LONG, this.toString());
		}
		vos.writeShortNat(this.workerId);
		vos.writeLongNat(this.uid);
		vos.writeShortNat((short) this.level);
	}

  public abstract TLCState bind(UniqueString name, IValue value);
  public abstract TLCState bind(SymbolNode id, IValue value);  
  public abstract TLCState unbind(UniqueString name);
  /**
   * Convenience method when performance doesn't matter.
   */
  public IValue lookup(String var) {
	  return lookup(UniqueString.uniqueStringOf(var));
  }
  public abstract IValue lookup(UniqueString var);
  public abstract boolean containsKey(UniqueString var);
  public abstract TLCState copy();
  public abstract TLCState deepCopy();
  public abstract StateVec addToVec(StateVec states);
  public abstract void deepNormalize();
  public abstract long fingerPrint();
  public abstract boolean allAssigned();
  public abstract Set<OpDeclNode> getUnassigned();
  public abstract TLCState createEmpty();

  protected TLCState copy(TLCState copy) {
	  copy.level = this.level;
	  return copy;
  }
  
  protected TLCState deepCopy(TLCState copy) {
	  copy.level = this.level;
	  copy.workerId = this.workerId;
	  copy.uid = this.uid;
	  return copy;
  }
  
  public boolean noneAssigned() {
		// isEmpty just checks referential equality, which is broken when some code
		// invokes TLCState#copy on the empty state (e.g. FcnRcdValue).
		return getUnassigned().size() >= vars.length;
  }

  /** 
   * Returns a mapping of variable names to their assigned values in this state.
   */ 
  public final Map<UniqueString, IValue> getVals() {
	final Map<UniqueString, IValue> valMap = new HashMap<UniqueString, IValue>();
	for(int i = 0; i < vars.length; i++) {
        UniqueString key = vars[i].getName();
        IValue val = this.lookup(key);
        valMap.put(key, val);
    }
    return valMap;
  }
  
  public final OpDeclNode[] getVars() {
	  return vars;
  }
  
  public final String[] getVarsAsStrings() {
	  String[] res = new String[vars.length];
	  for (int i = 0; i < vars.length; i++) {
		res[i] = vars[i].getName().toString();
	  }
	  return res;
  }

  public TLCState setPredecessor(final TLCStateInfo predecessor) {
	  return setPredecessor(predecessor.getOriginalState());
  }

  public TLCState setPredecessor(final TLCState predecessor) {
	  // This method only keeps the level instead of the predecessor, because a) we
	  // don't need the predecessor and b) keeping predecessors would mean that we
	  // eventually have all states of the state graph in memory.
	  if (predecessor.getLevel() == Integer.MAX_VALUE) {
		  Assert.fail(EC.TLC_TRACE_TOO_LONG, this.toString());
	  }
	  this.level = predecessor.getLevel() + 1;
	  return this;
  }

  public TLCState unsetPredecessor() {
	  return this;
  }
 
  public TLCState getPredecessor() {
	  return null;
  }

  public final int getLevel() {
	return this.level;  
  }
  
  public final boolean isInitial() {
	return this.level == INIT_LEVEL;
  }
  
  /* Returns a string representation of this state.  */
  public abstract String toString();
  public abstract String toString(TLCState lastState);
  
  public Object execCallable() throws Exception {
	  // no-op - see TLAPlusExecutorState
	  return null;
  }
  
  public void setCallable(Callable<?> cl) {
	  // no-op - see TLAPlusExecutorState
  }

	public Action getAction() {
		  // no-op - see TLCStateMutExt
		return null;
	}

	public TLCState setAction(Action action) {
		  // no-op - see TLCStateMutExt
		return this;
	}

	public boolean hasAction() {
		return getAction() != null;
	}

	public Value getCached(int key) {
		return null;
	}

	public Value setCached(int key, Value value) {
		return null;
	}
	
	public TLCState evalStateLevelAlias() {
		return this;
	}

	/**
	 * Construct a state t such that its values are equal to the values of the
	 * current state for which the corresponding value in the prototype is non-null.
	 */
	public TLCState copyWith(final TLCState prototype) {
		final TLCState s = createEmpty();
		for(int i = 0; i < vars.length; i++) {
	        final UniqueString key = vars[i].getName();
	        final IValue val = prototype.lookup(key);
	        if (val != null) {
	        	s.bind(key, this.lookup(key));
	        }
	    }
		return this.copy(s);
	}

	/**
	 * Determine if <code>s1</code> is a subset of <code>s2</code> (i.e. <code>s1</code> has the same value
	 * as <code>s2</code> for every variable that <code>s2</code> has a value for).
	 *
	 * <p>In TLA+, a "state" defines a value for every variable in the universe, not just the ones defined
	 * in your spec.  In that sense, a {@link TLCState} really represents a <i>set</i> of states.  For
	 * instance, the {@link TLCState} <code>a = 1 /\ b = 2</code> includes every TLA+ state where
	 * <code>a = 1</code> and <code>b = 2</code>, including some states where <code>c = 3</code> and some
	 * states where <code>c = 100</code>.  The {@link TLCState}s {@link #Null} and {@link #Empty} represent
	 * the set of all states.
	 *
	 * <p>This function treats <code>s1</code> and <code>s2</code> as sets of states and determines if the
	 * first is a subset of the second.  Note that the result might not be knowable, since the values in
	 * the two states might not be comparable (see "Comparability" in the docstring for {@link IValue}).
	 *
	 * @param s1 the first set of states
	 * @param s2 the second set of states
	 * @return whether <code>s1</code> represents a subset of the states of <code>s2</code>
	 */
	public static PartialBoolean isSubset(TLCState s1, TLCState s2) {
		if (s2 == null || s2 == Empty) {
			return PartialBoolean.YES;
		}

		if (s1 == null) {
			s1 = Empty;
		}

		// Optimization: if the arguments point to the same state, then we can return true
		// without inspecting the state's contents.
		if (s1 == s2) {
			return PartialBoolean.YES;
		}

		try {
			for (OpDeclNode var : vars) {
				UniqueString key = var.getName();
				IValue val2 = s2.lookup(key);
				if (val2 != null) {
					IValue val1 = s1.lookup(key);
					if (!Objects.equals(val1, val2)) {
						return PartialBoolean.NO;
					}
				}
			}
		} catch (FingerprintException | Assert.TLCRuntimeException e) {
			// These exceptions get thrown when two values are not comparable.
			return PartialBoolean.MAYBE;
		}

		return PartialBoolean.YES;
	}

}
