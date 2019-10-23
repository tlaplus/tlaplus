// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:21:01 PST by lamport
//      modified on Sat Nov 13 12:43:44 PST 1999 by yuanyu

package tlc2.value.impl;

import tlc2.tool.FingerprintException;
import tlc2.util.Vect;
import tlc2.value.IValue;
import tlc2.value.Values;
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

  @Override
  public final byte getKind() { return OPRCDVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      Assert.fail("Attempted to compare operator " + Values.ppr(this.toString()) +
      " with value:\n" + Values.ppr(obj.toString()));
      return 0;         // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      Assert.fail("Attempted to check equality of operator " + Values.ppr(this.toString()) +
      " with value:\n" + Values.ppr(obj.toString()));
      return false;     // make compiler happy
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
      "\nis an element of operator " + Values.ppr(this.toString()));
      return false;     // make compiler happy
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
      " is a finite set.");
      return false;     // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final void addLine(Vect vs) {
    try {
      int len = vs.size();
      Value[] args = new Value[len-2];
      for (int i = 0; i < len-2; i++) {
        args[i] = (Value)vs.elementAt(i+1);
      }
      this.domain.addElement(args);
      this.values.addElement(vs.elementAt(len-1));
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
      int sz = this.domain.size();
      for (int i = 0; i < sz; i++) {
        Value[] vals = (Value[])this.domain.elementAt(i);
        if (args.length != vals.length) {
          Assert.fail("Attempted to apply the operator " + Values.ppr(this.toString()) +
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
      String msg = "Attempted to apply operator:\n" + Values.ppr(this.toString()) +
        "\nto arguments (";
      if (args.length > 0) msg += args[0];
      for (int i = 1; i < args.length; i++) {
        msg += ", " + args[i];
      }
      Assert.fail(msg +  "), which is undefined.");
      return null;     // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value select(Value arg) {
    try {
      Assert.fail("Attempted to call OpRcdValue.select(). This is a TLC bug.");
      return null;   // make compiler happy
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
      Values.ppr(this.toString()) + ".");
      return null;     // make compiler happy
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
      Values.ppr(this.toString()) + ".");
      return null;     // make compiler happy
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
      Values.ppr(this.toString()) + ".");
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
      Values.ppr(this.toString()) + ".");
      return 0;         // make compiler happy
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
  public final boolean isDefined() {
    try {
      boolean defined = true;
      for (int i = 0; i < this.values.size(); i++) {
        defined = defined && ((Value)this.values.elementAt(i)).isDefined();
      }
      return defined;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

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

  /* Pretty-printing  */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      sb.append("{ ");
      if (this.values.size() != 0) {
        sb.append("<");
        Value[] args = (Value[])this.domain.elementAt(0);
        for (int j = 0; j < args.length; j++) {
          sb = args[j].toString(sb, offset, swallow);
          sb.append(", ");
        }
        sb = ((Value)this.values.elementAt(0)).toString(sb, offset, swallow);
        sb.append(">");
      }
      for (int i = 1; i < this.values.size(); i++) {
        sb.append(", <");
        Value[] args = (Value[])this.domain.elementAt(i);
        for (int j = 0; j < args.length; j++) {
          sb = args[j].toString(sb, offset, swallow);
          sb.append(", ");
        }
        sb = ((Value)this.values.elementAt(i)).toString(sb, offset, swallow);
        sb.append(">");
      }
      return sb.append("}");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

}
