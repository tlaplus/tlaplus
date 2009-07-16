// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:01 PST by lamport
//      modified on Sat Nov 13 12:43:44 PST 1999 by yuanyu

package tlc2.value;

import tlc2.util.Vect;
import util.Assert;
import util.WrongInvocationException;

public class OpRcdValue extends OpValue implements Applicable {
  public Vect domain;
  public Vect values;
  
  /* Constructor */
  public OpRcdValue() {
    this.domain = new Vect();
    this.values = new Vect();
  }

  public OpRcdValue(Vect domain, Vect values) {
    this.domain = domain;
    this.values = values;
  }

  public final byte getKind() { return OPRCDVALUE; }

  public final int compareTo(Object obj) {
    Assert.fail("Attempted to compare operator " + ppr(this.toString()) +
		" with value:\n" + ppr(obj.toString()));
    return 0;         // make compiler happy
  }
  
  public final boolean equals(Object obj) {
    Assert.fail("Attempted to check equality of operator " + ppr(this.toString()) +
		" with value:\n" + ppr(obj.toString()));
    return false;     // make compiler happy
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
		"\nis an element of operator " + ppr(this.toString()));
    return false;     // make compiler happy
  }

  public final boolean isFinite() {
    Assert.fail("Attempted to check if the operator " + ppr(this.toString()) +
		" is a finite set.");
    return false;     // make compiler happy
  }
  
  public final void addLine(Vect vs) {
    int len = vs.size();
    Value[] args = new Value[len-2];
    for (int i = 0; i < len-2; i++) {
      args[i] = (Value)vs.elementAt(i+1);
    }
    this.domain.addElement(args);
    this.values.addElement(vs.elementAt(len-1));
  }

  public final Value apply(Value arg, int control) {
      throw new WrongInvocationException("Should use the other apply method.");
  }

  public final Value apply(Value[] args, int control) {
    int sz = this.domain.size();
    for (int i = 0; i < sz; i++) {
      Value[] vals = (Value[])this.domain.elementAt(i);
      if (args.length != vals.length) {
	Assert.fail("Attempted to apply the operator " + ppr(this.toString()) +
		    "\nwith wrong number of arguments.");
      }
      boolean matched = true;
      for (int j = 0; j < vals.length; j++) {
	matched = vals[j].equals(args[j]);
	if (!matched) break;
      }
      if (matched) {
	return (Value)this.values.elementAt(i);
      }
    }
    // Generate the error message:
    String msg = "Attempted to apply operator:\n" + ppr(this.toString()) +
      "\nto arguments (";
    if (args.length > 0) msg += args[0];
    for (int i = 1; i < args.length; i++) {
      msg += ", " + args[i];
    }
    Assert.fail(msg +  "), which is undefined.");
    return null;     // make compiler happy
  }

  public final Value select(Value arg) {
    Assert.fail("Attempted to call OpRcdValue.select(). This is a TLC bug.");
    return null;   // make compiler happy    
  }

  public final Value takeExcept(ValueExcept ex) {
    Assert.fail("Attempted to appy EXCEPT construct to the operator " +
		ppr(this.toString()) + ".");
    return null;     // make compiler happy
  }

  public final Value takeExcept(ValueExcept[] exs) {
    Assert.fail("Attempted to apply EXCEPT construct to the operator " +
		ppr(this.toString()) + ".");
    return null;     // make compiler happy
  }

  public final Value getDomain() {
    Assert.fail("Attempted to compute the domain of the operator " +
		ppr(this.toString()) + ".");
    return EmptySet;   // make compiler happy
  }
  
  public final int size() {
    Assert.fail("Attempted to compute the number of elements in the operator " +
		ppr(this.toString()) + ".");
    return 0;         // make compiler happy
  }

  /* Should never normalize an operator. */
  public final boolean isNormalized() {
      throw new WrongInvocationException("Should not normalize an operator.");
  }
  
  public final void normalize() {
      throw new WrongInvocationException("Should not normalize an operator.");
  }

  public final boolean isDefined() {
    boolean defined = true;
    for (int i = 0; i < this.values.size(); i++) {
      defined = defined && ((Value)this.values.elementAt(i)).isDefined();
    }
    return defined;
  }
  
  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
      throw new WrongInvocationException("Should not initialize an operator.");
  }

  /* Pretty-printing  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    sb.append("{ ");
    if (this.values.size() != 0) {
      sb.append("<");
      Value[] args = (Value[])this.domain.elementAt(0);
      for (int j = 0; j < args.length; j++) {
	sb = args[j].toString(sb, offset);
	sb.append(", ");	
      }
      sb = ((Value)this.values.elementAt(0)).toString(sb, offset);
      sb.append(">");
    }
    for (int i = 1; i < this.values.size(); i++) {
      sb.append(", <");
      Value[] args = (Value[])this.domain.elementAt(i);
      for (int j = 0; j < args.length; j++) {
	sb = args[j].toString(sb, offset);
	sb.append(", ");	
      }
      sb = ((Value)this.values.elementAt(i)).toString(sb, offset);
      sb.append(">");
    }
    return sb.append("}");
  }

}
