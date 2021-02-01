// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 15:30:09 PST by lamport
//      modified on Fri Sep 22 13:18:45 PDT 2000 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.FingerprintException;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.Values;
import util.Assert;
import util.WrongInvocationException;

public class OpLambdaValue extends OpValue implements Applicable {
  public final OpDefNode opDef;       // the operator definition.
  public final ITool tool;
  public final Context con;
  public final TLCState state;
  public final TLCState pstate;

  /* Constructor */
  public OpLambdaValue(OpDefNode op, ITool tool,	Context con,
           TLCState state, TLCState pstate) {
    this.opDef = op;
    this.tool = tool;
    this.state = state;
    this.con = con;
    this.pstate = pstate;
  }

  public OpLambdaValue(OpDefNode op, ITool tool,	Context con,
          TLCState state, TLCState pstate, CostModel cm) {
	this(op, tool, con, state, pstate);
	this.cm = cm;
  }
  
  public OpLambdaValue(OpLambdaValue other, ITool tool) {
	  this(other.opDef, tool, other.con, other.state, other.pstate);
  }

  @Override
  public final byte getKind() { return OPLAMBDAVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      Assert.fail("Attempted to compare operator " + Values.ppr(this.toString()) +
      " with value:\n" + Values.ppr(obj.toString()), getSource());
      return 0;       // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      Assert.fail("Attempted to check equality of operator " + Values.ppr(this.toString()) +
      " with value:\n" + Values.ppr(obj.toString()), getSource());
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean member(Value elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
      "\nis an element of operator " + Values.ppr(this.toString()), getSource());
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the operator " + Values.ppr(this.toString()) +
      " is a finite set.", getSource());
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value apply(Value arg, int control) {
    try {
      throw new WrongInvocationException("Should use the other apply method.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value apply(Value[] args, int control) {
    try {
      int alen = this.opDef.getArity();
      if (alen != args.length) {
        Assert.fail("Applying the operator " + Values.ppr(this.toString()) +
        " with wrong number of arguments.", getSource());
      }
      Context c1 = this.con;
      FormalParamNode[] formals = this.opDef.getParams();
      for (int i = 0; i < alen; i++) {
        c1 = c1.cons(formals[i], args[i]);
      }
      return (Value) this.tool.eval(this.opDef.getBody(), c1, this.state, this.pstate,
          control);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value select(Value arg) {
    try {
      throw new WrongInvocationException("Error(TLC): attempted to call OpLambdaValue.select().");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept ex) {
    try {
      Assert.fail("Attempted to appy EXCEPT construct to the operator " +
      Values.ppr(this.toString()) + ".", getSource());
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept[] exs) {
    try {
      Assert.fail("Attempted to apply EXCEPT construct to the operator " +
      Values.ppr(this.toString()) + ".", getSource());
      return null;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value getDomain() {
    try {
      Assert.fail("Attempted to compute the domain of the operator " +
      Values.ppr(this.toString()) + ".", getSource());
      return SetEnumValue.EmptySet;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final int size() {
    try {
      Assert.fail("Attempted to compute the number of elements in the operator " +
      Values.ppr(this.toString()) + ".", getSource());
      return 0;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* Should never normalize an operator. */
  @Override
  public final boolean isNormalized() {
    try {
      throw new WrongInvocationException("Should not normalize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value normalize() {
    try {
      throw new WrongInvocationException("Should not normalize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isDefined() { return true; }

  @Override
  public final IValue deepCopy() { return this; }

  @Override
  public final boolean assignable(Value val) {
    try {
      throw new WrongInvocationException("Should not initialize an operator.");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* String representation of the value.  */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean ignored) {
    try {
      String opName = this.opDef.getName().toString();
      return sb.append("<Operator ").append(opName).append(">");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

}
