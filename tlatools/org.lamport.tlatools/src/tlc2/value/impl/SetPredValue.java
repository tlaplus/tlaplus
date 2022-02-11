// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Thu  5 Jul 2007 at  4:44:23 PST by lamport
//      modified on Fri Aug 10 15:10:04 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.IBoolValue;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

public class SetPredValue extends EnumerableValue implements Enumerable {
  public final Object vars;           // FormalParamNode or FormalParamNode[]
    /***********************************************************************
    * Was OpDeclNode or OpDeclNode[].                                      *
    ***********************************************************************/
  public Value inVal;           // the in value or the real set
  public final SemanticNode pred;     // the predicate
  public final ITool tool;             // null iff inVal is the real set
  /**
   * true after inVal has been converted to a SetEnumValue.  I assume this
   * implies (inVal instanceof SetEnumValue) too but the serialization
   * might interfere.
   * MAK 07/18/2019
   */
  private boolean converted = false; 
  public final Context con;
  public final TLCState state;
  public final TLCState pstate;
  public final int control;

  /* Constructor */
  public SetPredValue(Object vars, Value  inVal, SemanticNode pred, ITool tool,
          Context con, TLCState s0, TLCState s1, int control) {
    this.vars = vars;
    this.inVal = inVal;
    this.pred = pred;
    this.tool = tool;
    this.con = con;
    this.state = s0.copy();
    if (s1 != null) {
        this.pstate = s1.copy();
    } else {
        this.pstate = null;
    }
      /**
       * The two copy()s above were added by YY on 12 Mar 2010 to fix the
       * following bug: When a lazily evaluated expression is saved, the
       * state under which it should be evaluated must be saved.  The
       * s0 and s1 objects with which this method is called can be modified
       * after the call, so copies must be made.
       */
    this.control = control;
  }

  public SetPredValue(Object vars, Value  inVal, SemanticNode pred, ITool tool,
          Context con, TLCState s0, TLCState s1, int control, CostModel cm) {
	  this(vars, inVal, pred, tool, con, s0, s1, control);
	  this.cm = cm;
  }
  
	public SetPredValue(SetPredValue other, ITool tool) {
		this(other.vars, other.inVal, other.pred, tool, other.con, other.state, other.pstate, other.control, other.cm);
	}

  @Override
  public final byte getKind() { return SETPREDVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      this.inVal = this.toSetEnum();
      this.converted = true;
      return this.inVal.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      this.inVal = this.toSetEnum();
      this.converted = true;
      return this.inVal.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean member(Value elem) {
    try {
      if (this.converted) {
        return this.inVal.member(elem);
      }
      try {
        if (this.inVal.member(elem)) {
          Context con1 = this.con;
          if (this.vars instanceof FormalParamNode) {
            con1 = con1.cons((FormalParamNode)this.vars, elem);
          }
          else {
            FormalParamNode[] ids = (FormalParamNode[])this.vars;
            TupleValue tv = (TupleValue) elem.toTuple();
            if ((tv != null) && (tv.elems.length == ids.length)) {
              Value [] vals = ((TupleValue)tv).elems;
              for (int i = 0; i < ids.length; i++) {
                con1 = con1.cons(ids[i], vals[i]);
              }
            }
            else {
              Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
              "\nis an element of a set of " + ids.length + "-tuples.", getSource());
            }
          }
          Value  res = (Value) this.tool.eval(this.pred, con1, this.state, this.pstate, this.control);
          if (!(res instanceof IBoolValue)) {
            Assert.fail("The evaluation of predicate " + this.pred +
                  " yielded non-Boolean value.", getSource());
          }
          return ((BoolValue)res).val;
        }
      }
      catch (EvalException e) {
        Assert.fail("Cannot decide if element:\n" + Values.ppr(elem.toString()) +
        "\n is element of:\n" + Values.ppr(this.inVal.toString()) +
        "\nand satisfies the predicate " + this.pred, getSource());
      }
      return false;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      if (!(this.inVal.isFinite())) {
        Assert.fail("Attempted to check if expression of form {x \\in S : p(x)} is a " +
        "finite set, but cannot check if S:\n" + Values.ppr(this.inVal.toString()) +
        "\nis finite.", getSource());
      }
      return true;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT to the set " + Values.ppr(this.toString()) + ".", getSource());
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT to the set " + Values.ppr(this.toString()) + ".", getSource());
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final int size() {
    try {
      this.inVal = this.toSetEnum();
      this.converted = true;
      return this.inVal.size();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final void readObject(ObjectInputStream ois) throws IOException, ClassNotFoundException {
    this.inVal = (Value )ois.readObject();
    this.converted = true;
  }

  private final void writeObject(ObjectOutputStream oos) throws IOException {
    if (!this.converted) {
      this.inVal = this.toSetEnum();
      this.converted = true;
    }
    oos.writeObject(this.inVal);
  }

  /* This method normalizes (destructively) this set. */
  @Override
  public final boolean isNormalized() {
    try {
      return this.inVal.isNormalized();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value normalize() {
    try {
      this.inVal.normalize();
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final void deepNormalize() {
	  try {
      inVal.deepNormalize();
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
      return this.equals(val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The fingerprint method */
  @Override
  public final long fingerPrint(long fp) {
    try {
      this.inVal = this.toSetEnum();
      this.converted = true;
      return this.inVal.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) {
    try {
      this.inVal = this.toSetEnum();
      this.converted = true;
      return this.inVal.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public Value toSetEnum() {
      if (this.converted) {
    	  return (SetEnumValue) this.inVal;
      }
      ValueVec vals = new ValueVec();
      ValueEnumeration Enum = this.elements();
      Value  elem;
      while ((elem = Enum.nextElement()) != null) {
        vals.addElement(elem);
      }
      if (coverage) {cm.incSecondary(vals.size());}
      return new SetEnumValue(vals, this.isNormalized(), cm);
  }

  @Override
  public void write(final IValueOutputStream vos) throws IOException {
	  inVal.write(vos);
  }

  /* The string representation of the value. */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      try {
        if (TLCGlobals.expand) {
          Value  val = this.toSetEnum();
          return val.toString(sb, offset, swallow);
        }
      }
      catch (Throwable e) { if (!swallow) throw e; }

      sb.append("{");
      if (this.vars instanceof FormalParamNode) {
        sb.append(((FormalParamNode)this.vars).getName());
      }
      else {
        FormalParamNode[] ids = (FormalParamNode[])this.vars;
        if (ids.length != 0) sb.append(ids[0].getName());
        for (int i = 1; i < ids.length; i++) {
          sb.append(", " + ids[i].getName());
        }
      }
      sb.append(" \\in " + this.inVal + " : <expression ");
      sb.append(this.pred + "> }");
      return sb;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final ValueEnumeration elements() {
    try {
      if (this.converted) {
        return ((SetEnumValue)this.inVal).elements();
      }
      return new Enumerator();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  final class Enumerator implements ValueEnumeration {
    ValueEnumeration Enum;

    public Enumerator() {
      if (!(inVal instanceof Enumerable)) {
        Assert.fail("Attempted to enumerate { x \\in S : p(x) } when S:\n" +
              Values.ppr(inVal.toString()) + "\nis not enumerable", getSource());
      }
      this.Enum = ((Enumerable)inVal).elements();
    }

    @Override
    public final void reset() { this.Enum.reset(); }

    @Override
    public final Value nextElement() {
    	Value  elem;
      while ((elem = this.Enum.nextElement()) != null) {
    	  if (coverage) { cm.incSecondary(); }
        Context con1 = con;
        if (vars instanceof FormalParamNode) {
          con1 = con1.cons((FormalParamNode)vars, elem);
        }
        else {
          FormalParamNode[] ids = (FormalParamNode[])vars;
          TupleValue tv = (TupleValue) elem.toTuple();
          if ((tv != null) &&
              (((TupleValue)tv).elems.length == ids.length)) {
            Value [] vals = ((TupleValue)tv).elems;
            for (int i = 0; i < ids.length; i++) {
              con1 = con1.cons(ids[i], vals[i]);
            }
          }
          else {
            Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
            "\nis an element of a set of " + ids.length + "-tuples.", getSource());
          }
        }
        Value  res = (Value) tool.eval(pred, con1, state, pstate, control, cm);
        if (!(res instanceof IBoolValue)) {
          Assert.fail("Evaluating predicate " + pred + " yielded non-Boolean value.", getSource());
        }
        if (((BoolValue)res).val) return elem;
      }
      return null;
    }

  }

}
