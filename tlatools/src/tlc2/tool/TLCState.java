// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:58 PST by lamport
//      modified on Tue Oct 23 16:48:38 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SymbolNode;
import tlc2.output.EC;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.ValueOutputStream;
import util.Assert;
import util.UniqueString;

public abstract class TLCState implements Cloneable, Serializable {
  public short workerId = Short.MAX_VALUE; // Must be set to a non-negative number. Valid worker ids \in [0,Short.MAX_VALUE] and start at 0.
  public long uid = -1;   // Must be set to a non-negative number
  private int level = 1;
  
  // Set by subclasses. Cannot set until we know what the variables are.
  public static TLCState Empty = null;

  // The state variables.
  protected static OpDeclNode[] vars = null;

  public void read(IValueInputStream vis) throws IOException {
	this.workerId = vis.readShortNat();
	this.uid = vis.readLongNat();
    this.level = vis.readShortNat();
    assert this.level >= 0; // Should never overflow.
  }
  
	public void write(ValueOutputStream vos) throws IOException {
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

  public final void setPredecessor(final TLCState predecessor) {
	  if (predecessor.getLevel() == Integer.MAX_VALUE) {
		  Assert.fail(EC.TLC_TRACE_TOO_LONG, this.toString());
	  }
	  this.level = predecessor.getLevel() + 1;
  }

  public final int getLevel() {
	return this.level;  
  }
  
  public final boolean isInitial() {
	return this.level == 1;
  }
  
  /* Returns a string representation of this state.  */
  public abstract String toString();
  public abstract String toString(TLCState lastState);
}
