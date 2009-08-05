// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:09 PST by lamport
//      modified on Fri Sep 22 13:18:45 PDT 2000 by yuanyu

package tlc2.value;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Context;
import util.Assert;
import util.WrongInvocationException;

public class OpLambdaValue extends OpValue implements Applicable {
  public OpDefNode opDef;       // the operator definition.
  public Tool tool;
  public Context con;
  public TLCState state;
  public TLCState pstate;
  
  /* Constructor */
  public OpLambdaValue(OpDefNode op, Tool tool,	Context con,
		       TLCState state, TLCState pstate) {
    this.opDef = op;
    this.tool = tool;
    this.state = state;
    this.con = con;
    this.pstate = pstate;
  }

  public final byte getKind() { return OPLAMBDAVALUE; }

  public final int compareTo(Object obj) {
    Assert.fail("Attempted to compare operator " + ppr(this.toString()) +
		" with value:\n" + ppr(obj.toString()));
    return 0;       // make compiler happy
  }
  
  public final boolean equals(Object obj) {
    Assert.fail("Attempted to check equality of operator " + ppr(this.toString()) +
		" with value:\n" + ppr(obj.toString()));
    return false;   // make compiler happy
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
		"\nis an element of operator " + ppr(this.toString()));
    return false;   // make compiler happy
  }

  public final boolean isFinite() {
    Assert.fail("Attempted to check if the operator " + ppr(this.toString()) +
		" is a finite set.");
    return false;   // make compiler happy
  }

  public final Value apply(Value arg, int control) {
      throw new WrongInvocationException("Should use the other apply method.");
  }

  public final Value apply(Value[] args, int control) {
    int alen = this.opDef.getArity();
    if (alen != args.length) {
      Assert.fail("Applying the operator " + ppr(this.toString()) +
		  " with wrong number of arguments.");
    }
    Context c1 = this.con;
    FormalParamNode[] formals = this.opDef.getParams();    
    for (int i = 0; i < alen; i++) {
      c1 = c1.cons(formals[i], args[i]);
    }
    return this.tool.eval(this.opDef.getBody(), c1, this.state, this.pstate,
			  control);
  }

  public final Value select(Value arg) {
      throw new WrongInvocationException("Error(TLC): attempted to call OpLambdaValue.select().");
  }
  
  public final Value takeExcept(ValueExcept ex) {
    Assert.fail("Attempted to appy EXCEPT construct to the operator " +
		ppr(this.toString()) + ".");
    return null;   // make compiler happy
  }

  public final Value takeExcept(ValueExcept[] exs) {
    Assert.fail("Attempted to apply EXCEPT construct to the operator " +
		ppr(this.toString()) + ".");
    return null;   // make compiler happy
  }

  public final Value getDomain() {
    Assert.fail("Attempted to compute the domain of the operator " +
		ppr(this.toString()) + ".");
    return EmptySet;   // make compiler happy
  }
  
  public final int size() {
    Assert.fail("Attempted to compute the number of elements in the operator " +
		ppr(this.toString()) + ".");
    return 0;   // make compiler happy
  }

  /* Should never normalize an operator. */
  public final boolean isNormalized() {
      throw new WrongInvocationException("Should not normalize an operator.");
  }
  
  public final void normalize() {
      throw new WrongInvocationException("Should not normalize an operator.");
  }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
      throw new WrongInvocationException("Should not initialize an operator.");
  }

  /* String representation of the value.  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    String opName = this.opDef.getName().toString();
    return sb.append("<Operator ").append(opName).append(">");
  }

}
