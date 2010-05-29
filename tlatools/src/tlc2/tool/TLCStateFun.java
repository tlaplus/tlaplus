// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:58 PST by lamport
//      modified on Fri Jul 20 23:54:51 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;

import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.util.Context;
import tlc2.value.Value;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import util.UniqueString;
import util.WrongInvocationException;

/**
 * This class represents a TLA+ state, which simply is an assignment
 * of explicit values to the variables. This is the functional
 * version.  It is used for implementing the enabled predicate.  It
 * can not be used in getInitStates and getNextStates.
 */
public final class TLCStateFun extends TLCState {
  private SymbolNode name;
  private Value value;
  private TLCStateFun next;

  public final static TLCState Empty = new TLCStateFun(null, null, null);
  
  private TLCStateFun(SymbolNode name, Value value, TLCStateFun state) {
    this.name = name;
    this.value = value;
    this.next = state;
  }

  public final TLCState createEmpty() { return Empty; }

  public final TLCState bind(UniqueString name, Value value, SemanticNode expr) {
      throw new WrongInvocationException("TLCStateFun.bind: This is a TLC bug.");
  }

  public final TLCState bind(SymbolNode id, Value value, SemanticNode expr) {
    return new TLCStateFun(id, value, this);
  }
  
  public final TLCState unbind(UniqueString name) {
      throw new WrongInvocationException("TLCStateFun.unbind: This is a TLC bug.");
  }
  
  public final Value lookup(UniqueString var) {
    for (TLCStateFun cur = this; cur != Empty; cur = cur.next) {
      if (var == cur.name.getName()) return cur.value;
    }
    return null;
  }
  
  public final boolean containsKey(UniqueString var) {
    return this.lookup(var) != null;
  }
  
  public final TLCState copy() {
      // The following code added blindly by LL on 28 May 2010
      // to fix a bug.  I have no idea what's going on here.
       return new TLCStateFun(this.name, this.value, this.next);
      // throw new WrongInvocationException("TLCStateFun.copy: This is a TLC bug.");
  }
  
  public final TLCState deepCopy() {
      throw new WrongInvocationException("TLCStateFun.deepCopy: This is a TLC bug.");
  }
  
  public final void deepNormalize() {
      throw new WrongInvocationException("TLCStateFun.normalizeFcns: This is a TLC bug.");
  }
  
  public final long fingerPrint() {
      throw new WrongInvocationException("TLCStateFun.fingerPrint: This is a TLC bug.");
  }

  public final boolean allAssigned() { return true; }  

  public final Context addToContext(Context c) {
    Context c1 = c;
    for (TLCStateFun cur = this; cur != Empty; cur = cur.next) {
      c1 = c1.cons(cur.name, cur.value);
    }
    return c1;
  }

  public final StateVec addToVec(StateVec states) {
    return states.addElement(this);
  }
  
  public final void read(ValueInputStream vis) throws IOException {
      throw new WrongInvocationException("TLCStateFun.read: This is a TLC bug.");
  }

  public final void write(ValueOutputStream vos) throws IOException {
      throw new WrongInvocationException("TLCStateFun.write: This is a TLC bug.");
  }
  
  /* Returns a string representation of this state.  */
  public final String toString() {
    StringBuffer sb = new StringBuffer("[");
    if (this != Empty) {
      sb.append(this.name.getName().toString());
      sb.append(" -> ");
      sb.append(this.value.toString());

      for (TLCStateFun cur = this.next; cur != Empty; cur = cur.next) {
	sb.append(", ");
	sb.append(cur.name.getName().toString());
	sb.append("->");
	sb.append(cur.value);
      }
    }
    sb.append("]");
    return sb.toString();
  }
  
  public final String toString(TLCState lastState) {
      throw new WrongInvocationException("TLCStateFun.toString: This is a TLC bug.");
  }
  
}
