// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:02 PST by lamport
//      modified on Fri Aug 24 15:08:38 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;

import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.util.Context;
import tlc2.util.FP64;
import tlc2.util.ObjLongTable;
import tlc2.value.MVPerm;
import tlc2.value.Value;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import util.UniqueString;
import util.WrongInvocationException;

/**
 * This class represents a TLA+ state, which simply is an assignment
 * of explicit values to all the global variables.  This is the
 * mutable version, which means that in-place updates are used for
 * improved performance and reduced allocation.
 *
 * The viewMap was added by Rajeev Joshi.
 */
public final class TLCStateMutSource extends TLCState
implements Cloneable, Serializable {
  private Value[] values;
  private SemanticNode[] asts;
  private static Tool mytool = null;

  /**
   * If non-null, viewMap denotes the function to be applied to
   * a state before its fingerprint is computed.
   */
  private static SemanticNode viewMap = null;

  /**
   * If non-null, perms denotes the set of permutations under
   * the symmetry assumption.
   */
  private static MVPerm[] perms = null;

  private TLCStateMutSource(Value[] vals, SemanticNode[] asts) {
    this.values = vals;
    this.asts = asts;
  }

  public static void init(Tool tool) {
    mytool = tool;
    Value[] vals = new Value[vars.length];
    SemanticNode[] snodes = new SemanticNode[vars.length];
    Empty = new TLCStateMutSource(vals, snodes);
    viewMap = tool.getViewSpec();
    perms = tool.getSymmetryPerms();
  }

  public final TLCState createEmpty() {
    int sz = vars.length;
    return new TLCStateMutSource(new Value[sz], new SemanticNode[sz]);
  }

  public final boolean equals(Object obj) {
    if (obj instanceof TLCStateMutSource) {
      TLCStateMutSource state = (TLCStateMutSource)obj;
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

  public final TLCState bind(UniqueString name, Value value, SemanticNode ast) {
    int loc = name.getVarLoc();
    this.values[loc] = value;
    if (this.asts != null) {
      this.asts[loc] = ast;
    }
    return this;
  }

  public final TLCState bind(SymbolNode id, Value value, SemanticNode expr) {
    throw new WrongInvocationException("TLCStateMutSource.bind: This is a TLC bug.");
  }
  
  public final TLCState unbind(UniqueString name) {
    int loc = name.getVarLoc();
    this.values[loc] = null;
    this.asts[loc] = null;
    return this;
  }
  
  public final Value lookup(UniqueString var) {
    int loc = var.getVarLoc();
    if (loc < 0) return null;    
    return this.values[loc];
  }

  public final boolean containsKey(UniqueString var) {
    return (this.lookup(var) != null);
  }

  public final TLCState copy() {
    int len = this.values.length;
    Value[] vals = new Value[len];
    SemanticNode[] astClone = new SemanticNode[len];
    for (int i = 0; i < len; i++) {
      vals[i] = this.values[i];
      astClone[i] = this.asts[i];
    }
    return new TLCStateMutSource(vals, astClone);
  }

  public final TLCState deepCopy() {
    int len = this.values.length;
    Value[] vals = new Value[len];
    SemanticNode[] astClone = new SemanticNode[len];
    for (int i = 0; i < len; i++) {
      Value val = this.values[i];
      if (val != null) {
	vals[i] = val.deepCopy();
	astClone[i] = this.asts[i];
      }
    }
    return new TLCStateMutSource(vals, astClone);
  }

  public final StateVec addToVec(StateVec states) {
    return states.addElement(this.copy());
  }
  
  public final void deepNormalize() {
    for (int i = 0; i < this.values.length; i++) {
      Value val = this.values[i];
      if (val != null) {
	val.deepNormalize();
      }
    }
  }

  private final void readObject(ObjectInputStream ois)
  throws IOException, ClassNotFoundException {
    this.values = (Value[])ois.readObject();
    this.asts = null;
  }

  private final void writeObject(ObjectOutputStream oos) throws IOException {
    oos.writeObject(this.values);
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

    Value[] minVals = this.values;
    if (perms != null) {
      Value[] vals = new Value[sz];
      // Find the "smallest" state under the symmetry permutations:
      for (int i = 0; i < perms.length; i++) {
	int cmp = 0;
	for (int j = 0; j < sz; j++) {
	  vals[j] = this.values[j].permute(perms[i]);
	  if (cmp == 0) {
	    cmp = vals[j].compareTo(minVals[j]);
	  }
	}
	if (cmp < 0) {
	  if (minVals == this.values) {
	    minVals = vals;
	    vals = new Value[sz];
	  }
	  else {
	    Value[] temp = minVals;
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
    }
    else {
      for (int i = 0; i < sz; i++) {
	this.values[i].deepNormalize();
      }
      TLCStateMutSource state = this;
      if (minVals != this.values) {
	state = new TLCStateMutSource(minVals, this.asts);
      }
      Value val = mytool.eval(viewMap, Context.Empty, state);
      fp = val.fingerPrint(fp);
    }
    return fp;
  }

  public final void addCounts(ObjLongTable counts) {
    for (int i = 0; i < this.asts.length; i++) {
      counts.add(this.asts[i], 1);
    }      
  }

  public final boolean allAssigned() {
    int len = this.values.length;    
    for (int i = 0; i < len; i++) {
      if (values[i] == null) return false;
    }
    return true;
  }

  public final void read(ValueInputStream vis) throws IOException {
    super.read(vis);    
    int len = this.values.length;
    for (int i = 0; i < len; i++) {
      this.values[i] = vis.read();
    }
  }

  public final void write(ValueOutputStream vos) throws IOException {
    super.write(vos);    
    int len = this.values.length;
    for (int i = 0; i < len; i++) {
      vos.write(this.values[i]);
    }
  }
  
  /* Returns a string representation of this state.  */
  public final String toString() {
    if (TLCGlobals.useView && viewMap != null) {
      Value val = mytool.eval(viewMap, Context.Empty, this);
      return Value.ppr(val.toString());
    }
    StringBuffer result = new StringBuffer();
    int vlen = vars.length;
    if (vlen == 1) {
      UniqueString key = vars[0].getName();
      Value val = lookup(key);
      String val_str = (val == null) ? "null" : Value.ppr(val.toString());
      result.append(key.toString());
      result.append(" = " + val_str + "\n");
    }
    else {
      for (int i = 0; i < vlen; i++) {
	UniqueString key = vars[i].getName();
	Value val = lookup(key);
	String val_str = (val == null) ? "null" : Value.ppr(val.toString());
	result.append("/\\ ");
	result.append(key.toString());
	result.append(" = " + val_str + "\n");
      }
    }
    return result.toString();
  }

  /* Returns a string representation of this state.  */
  public final String toString(TLCState lastState) {
    StringBuffer result = new StringBuffer();
    TLCStateMutSource lstate = (TLCStateMutSource)lastState;

    int vlen = vars.length;
    if (vlen == 1) {
      UniqueString key = vars[0].getName();
      Value val = this.lookup(key);
      Value lstateVal = lstate.lookup(key);
      if (!val.equals(lstateVal)) {
	String val_str = (val == null) ? "null" : Value.ppr(val.toString());
	result.append(key.toString());
	result.append(" = " + val_str + "\n");
      }
    }
    else {
      for (int i = 0; i < vlen; i++) {
	UniqueString key = vars[i].getName();
	Value val = this.lookup(key);
	Value lstateVal = lstate.lookup(key);
	if (!val.equals(lstateVal)) {
	  String val_str = (val == null) ? "null" : Value.ppr(val.toString());
	  result.append("/\\ ");
	  result.append(key.toString());
	  result.append(" = " + val_str + "\n");
	}
      }
    }
    return result.toString();
  }

}
