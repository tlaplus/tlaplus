// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:01 PST by lamport
//      modified on Wed Dec  5 23:18:37 PST 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.io.Serializable;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.Callable;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.util.Context;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import tlc2.value.impl.Value;
import util.UniqueString;
import util.WrongInvocationException;

/**
 * Attention! Copy of TLCStateMut except for getter/setter and fields callable,
 * predecessor and action.
 */
public final class TLCStateMutExt extends TLCState implements Cloneable, Serializable {
  private IValue values[];
  private static ITool mytool = null;

  /**
   * If non-null, viewMap denotes the function to be applied to
   * a state before its fingerprint is computed.
   */
  private static SemanticNode viewMap = null;

  /**
   * If non-null, perms denotes the set of permutations under the
   * symmetry assumption.
   */
  private static IMVPerm[] perms = null;

  private TLCStateMutExt(IValue[] vals) { this.values = vals; }
  
  public static void setVariables(OpDeclNode[] variables) 
  {
      vars = variables;
      IValue[] vals = new IValue[vars.length];
      Empty = new TLCStateMutExt(vals);

      // SZ 10.04.2009: since this method is called exactly one from Spec#processSpec
      // moved the call of UniqueString#setVariables to that place
      
      // UniqueString[] varNames = new UniqueString[variables.length];
      // for (int i = 0; i < varNames.length; i++)
      // {
      //  varNames[i] = variables[i].getName();
      //}
      //UniqueString.setVariables(varNames);
  }

  public static void setTool(ITool tool) {
    mytool = tool;
    viewMap = tool.getViewSpec();
    perms = tool.getSymmetryPerms();
  }

  public final TLCState createEmpty() {
	  IValue[] vals = new IValue[vars.length];
    return new TLCStateMutExt(vals);
  }

  //TODO equals without hashcode!
  public final boolean equals(Object obj) {
    if (obj instanceof TLCStateMutExt) {
      TLCStateMutExt state = (TLCStateMutExt)obj;
      for (int i = 0; i < this.values.length; i++) {
	if (this.values[i] == null) {
	  if (state.values[i] != null) return false;
	}
	else if (state.values[i] == null ||
		 !this.values[i].equals(state.values[i])) {
	  return false;
	}
      }
      return true;
    }
    return false;
  }
  
  public final TLCState bind(UniqueString name, IValue value) {
	  // Note, tla2sany.semantic.OpApplNode.toString(Value) relies on this ordering.
    int loc = name.getVarLoc();
    this.values[loc] = value;
    return this;
  }

  public final TLCState bind(SymbolNode id, IValue value) {
    throw new WrongInvocationException("TLCStateMut.bind: This is a TLC bug.");
  }
  
  public final TLCState unbind(UniqueString name) {
    int loc = name.getVarLoc();
    this.values[loc] = null;
    return this;
  }

  public final IValue lookup(UniqueString var) {
    int loc = var.getVarLoc();
    if (loc < 0) return null;
    return this.values[loc];
  }

  public final boolean containsKey(UniqueString var) {
    return (this.lookup(var) != null);
  }

  public final TLCState copy() {
    int len = this.values.length;
    IValue[] vals = new IValue[len];
    for (int i = 0; i < len; i++) {
      vals[i] = this.values[i];
    }
    return copyExt(new TLCStateMutExt(vals));
  }

  public final TLCState deepCopy() {
    int len = this.values.length;
    IValue[] vals = new IValue[len];
    for (int i = 0; i < len; i++) {
      IValue val = this.values[i];
      if (val != null) {
	vals[i] = val.deepCopy();
      }
    }
	return deepCopy(new TLCStateMutExt(vals));
  }

  public final StateVec addToVec(StateVec states) {
    return states.addElement(this.copy());
  }
  
  public final void deepNormalize() {
    for (int i = 0; i < this.values.length; i++) {
      IValue val = this.values[i];
      if (val != null) {
	val.deepNormalize();
      }
    }
  }

  /**
   * This method returns the fingerprint of this state. We fingerprint
   * the values in the state according to the order given by vars.
   * This guarantees the same state has the same fingerprint.
   *
   * Since the values in this state can be shared by multiple threads
   * via the state queue. They have to be normalized before adding to
   * the state queue.  We do that here.
   */
	public final long fingerPrint() {
		int sz = this.values.length;

		// TLC supports symmetry reduction. Symmetry reduction works by defining classes
		// of symmetrically equivalent states for which TLC only checks a
		// single representative of the equivalence class (orbit). E.g. in a two
		// process mutual exclusion problem, the process ids are - most of the time -
		// not relevant with regards to mutual exclusion: We don't care if process A or
		// B is in the critical section as long as only a single process is in CS. Thus
		// two states are symmetric that only differ in the process id variable value.
		// Symmetry can also be observed graphically in the state graph s.t. subgraphs
		// are isomorphic (Graph Isomorphism). Instead of enumerating the complete state
		// graph, TLC enumerates one of the isomorphic subgraphs whose state correspond
		// to the representatives. With respect to the corresponding Kripke structure M,
		// the resulting Kripke M' is called the "quotient structure" (see "Exploiting
		// Symmetry in Temporal Logic Model Checking" by Clarke et al).
		// 
		// The definition of equivalence classes (orbits) is provided manually by the
		// user at startup by defining 1 to n symmetry sets. Thus TLC has to find
		// representative at runtime only which happens below. Given any state s, TLC
		// evaluates rep(s) to find the lexicographically smallest state ss = rep(s)
		// with regards to the variable values. The state ss is then fingerprint instead
		// of s.
		//
		// Evaluating rep(s) - to reduce s to ss - requires to apply all permutations in
		// the group this.perms (derived from the user-defined orbit). This is known as
		// the constructive orbit problem and is NP-hard. The loop has O(|perms| * |this.values|)
		// with |prems| = |symmetry set 1|! * |symmetry set 2|! * ... * |symmetry set n|. 
        //		
		// minVals is what is used to calculate/generate the fingerprint below.
		// If this state is not the lexicographically smallest state ss, its current
		// minVals will be replaced temporarily with the values of ss for the
		// calculation of the fingerprint.
		IValue[] minVals = this.values;
		if (perms != null) {
			IValue[] vals = new IValue[sz];
			// The following for loop converges to the smallest state ss under symmetry by
			// looping over all permutations applying each. If the outcome turns out to be
			// lexicographically smaller than the currently smallest, it replaces the
			// current smallest. Once all permutations (perms) have been processed, we know
			// we have found the smallest state.
			NEXT_PERM: for (int i = 0; i < perms.length; i++) {
				int cmp = 0;
				// For each value in values succinctly permute the current value
				// and compare it to its corresponding minValue in minVals.
				for (int j = 0; j < sz; j++) {
					vals[j] = this.values[j].permute(perms[i]);
					if (cmp == 0) {
						// Only compare unless an earlier compare has found a
						// difference already (if a difference has been found
						// earlier, still permute the remaining values of the
						// state to fully permute all state values).
						cmp = vals[j].compareTo(minVals[j]);
						if (cmp > 0) {
							// When cmp evaluates to >0, all subsequent
							// applications of perms[i] for the remaining values
							// won't make the resulting vals[] smaller than
							// minVals. Thus, exit preemptively from the loop
							// over vals. This works because perms is the cross
							// product of all symmetry sets.
							continue NEXT_PERM;
						}
					}
				}
				// cmp < 0 means the current state is part of a symmetry
				// permutation set/group and not the "smallest" one.
				if (cmp < 0) {
					if (minVals == this.values) {
						minVals = vals;
						vals = new IValue[sz];
					} else {
						IValue[] temp = minVals;
						minVals = vals;
						vals = temp;
					}
				}
			}
		}
		// Fingerprint the state:
		long fp = FP64.New();
		if (viewMap == null) {
			for (int i = 0; i < sz; i++) {
				fp = minVals[i].fingerPrint(fp);
			}
			if (this.values != minVals) {
				for (int i = 0; i < sz; i++) {
					this.values[i].deepNormalize();
				}
			}
		} else {
			for (int i = 0; i < sz; i++) {
				this.values[i].deepNormalize();
			}
			TLCStateMutExt state = this;
			if (minVals != this.values) {
				state = new TLCStateMutExt(minVals);
			}
			IValue val = mytool.eval(viewMap, Context.Empty, state);
			fp = val.fingerPrint(fp);
		}
		return fp;
	}

  public final boolean allAssigned() {
    int len = this.values.length;    
    for (int i = 0; i < len; i++) {
      if (values[i] == null) return false;
    }
    return true;
  }

    @Override
	public boolean noneAssigned() {
		int len = this.values.length;
		for (int i = 0; i < len; i++) {
			if (values[i] != null) {
				return false;
			}
		}
		return true;
	}
 
    @Override
	public final Set<OpDeclNode> getUnassigned() {
		// Return sorted set (lexicographical).
		final Set<OpDeclNode> unassignedVars = new TreeSet<OpDeclNode>(new Comparator<OpDeclNode>() {
			@Override
			public int compare(OpDeclNode o1, OpDeclNode o2) {
				return o1.getName().toString().compareTo(o2.getName().toString());
			}
		});
		int len = this.values.length;
		for (int i = 0; i < len; i++) {
			if (values[i] == null) {
				unassignedVars.add(vars[i]);
			}
		}
		return unassignedVars;
	}

  public final void read(IValueInputStream vis) throws IOException {
    super.read(vis);
    int len = this.values.length;
    for (int i = 0; i < len; i++) {
      this.values[i] = vis.read();
    }
  }

  public final void write(IValueOutputStream vos) throws IOException {
    super.write(vos);
    int len = this.values.length;
    for (int i = 0; i < len; i++) {
    	this.values[i].write(vos);
    }
  }
  
  /* Returns a string representation of this state.  */
  public final String toString() {
    if (TLCGlobals.useView && viewMap != null) {
      IValue val = mytool.eval(viewMap, Context.Empty, this);
      return viewMap.toString(val);
    }
    StringBuffer result = new StringBuffer();
    int vlen = vars.length;
    if (vlen == 1) {
      UniqueString key = vars[0].getName();
      IValue val = this.lookup(key);
      result.append(key.toString());
      result.append(" = ");
      result.append(Values.ppr(val));
      result.append("\n");
    }
    else {
      for (int i = 0; i < vlen; i++) {
	UniqueString key = vars[i].getName();
	IValue val = this.lookup(key);
	result.append("/\\ ");
	result.append(key.toString());
    result.append(" = ");
    result.append(Values.ppr(val));
    result.append("\n");
      }
    }
    return result.toString();
  }
  
  /* Returns a string representation of this state.  */
  public final String toString(TLCState lastState) {
    StringBuffer result = new StringBuffer();
    TLCStateMutExt lstate = (TLCStateMutExt)lastState;

    int vlen = vars.length;
    if (vlen == 1) {
      UniqueString key = vars[0].getName();
      IValue val = this.lookup(key);
      IValue lstateVal = lstate.lookup(key);
      if (!lstateVal.equals(val)) {
	result.append(key.toString());
	result.append(" = " + Values.ppr(val) + "\n");
      }
    }
    else {
      for (int i = 0; i < vlen; i++) {
	UniqueString key = vars[i].getName();
	IValue val = this.lookup(key);
	IValue lstateVal = lstate.lookup(key);
	if (!lstateVal.equals(val)) {
	  result.append("/\\ ");
	  result.append(key.toString());
	  result.append(" = " + Values.ppr(val) + "\n");
	}
      }
    }
    return result.toString();
  }

	// *********//

	private Action action;

	@Override
	public Action getAction() {
		return action;
	}

	@Override
	public TLCState setAction(final Action action) {
		this.action = action;
		return this;
	}

	// *********//

	private TLCState predecessor;

	@Override
	public TLCState setPredecessor(final TLCState predecessor) {
		this.predecessor = predecessor;
		return super.setPredecessor(predecessor);
	}

	public TLCState getPredecessor() {
		return predecessor;
	}

	@Override
	public TLCState unsetPredecessor() {
		this.predecessor = null;
		return this;
	}

	// *********//

	@Override
	protected TLCState deepCopy(final TLCState copy) {
		super.deepCopy(copy);
		return copyExt(copy);
	}

	private TLCState copyExt(TLCState copy) {
		if (this.predecessor != null) {
			copy.setPredecessor(this.predecessor);
		}
		return copy.setAction(getAction());
	}

	// *********//

	private Callable<?> callable;

	@Override
	public Object execCallable() throws Exception {
		if (callable != null) {
			return callable.call();
		}
		return null;
	}

	@Override
	public void setCallable(Callable<?> f) {
		this.callable = f;
	}

	  private Map<Integer, Value> cache = new HashMap<>(0);
	  
		public Value getCached(final int key) {
			if (cache == null) {
				return null;
			}
			return cache.get(key);
		}

		public Value setCached(final int key, final Value value) {
			if (cache == null) {
				cache = new HashMap<>(0);
			}
			cache.put(key, value);
			return value;
		}
}
