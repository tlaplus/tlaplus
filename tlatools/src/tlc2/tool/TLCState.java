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
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.value.Value;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import util.UniqueString;

public abstract class TLCState implements Cloneable, Serializable {
  public long uid = -1;   // Must be set to a non-negative number
  public short level = 0;
  
  // Set by subclasses. Cannot set until we know what the variables are.
  public static TLCState Empty = null;

  // The state variables.
  protected static OpDeclNode[] vars = null;
  
  public static void setVariables(OpDeclNode[] variables) 
  {
      vars = variables;
      // SZ 10.04.2009: since this method is called exactly one from Spec#processSpec
      // moved the call of UniqueString#setVariables to that place
      
      // UniqueString[] varNames = new UniqueString[variables.length];
      // for (int i = 0; i < varNames.length; i++)
      // {
      //  varNames[i] = variables[i].getName();
      //}
      //UniqueString.setVariables(varNames);
  }

  public void read(ValueInputStream vis) throws IOException {
    this.uid = vis.readLongNat();
    this.level = vis.readShortNat();
    assert this.level >= 0; // Should never overflow.
  }
  
  public void write(ValueOutputStream vos) throws IOException {
    vos.writeLongNat(this.uid);
    vos.writeShortNat(this.level);
  }

  public abstract TLCState bind(UniqueString name, Value value, SemanticNode expr);
  public abstract TLCState bind(SymbolNode id, Value value, SemanticNode expr);  
  public abstract TLCState unbind(UniqueString name);
  public abstract Value lookup(UniqueString var);
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
  public Map<UniqueString, Value> getVals() {
	final Map<UniqueString, Value> valMap = new HashMap<UniqueString, Value>();
	for(int i = 0; i < vars.length; i++) {
        UniqueString key = vars[i].getName();
        Value val = this.lookup(key);
        valMap.put(key, val);
    }
    return valMap;
  }

  public boolean isInitial() {
	return this.level == 0;
  }
  
  /* Returns a string representation of this state.  */
  public abstract String toString();
  public abstract String toString(TLCState lastState);
}
