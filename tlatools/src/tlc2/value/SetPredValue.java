// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Thu  5 Jul 2007 at  4:44:23 PST by lamport
//      modified on Fri Aug 10 15:10:04 PDT 2001 by yuanyu

package tlc2.value;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.ModelChecker;
import tlc2.tool.FingerprintException;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Context;
import util.Assert;

public class SetPredValue extends EnumerableValue implements Enumerable {
  public Object vars;           // FormalParamNode or FormalParamNode[]
    /***********************************************************************
    * Was OpDeclNode or OpDeclNode[].                                      *
    ***********************************************************************/
  public Value inVal;           // the in value or the real set
  public SemanticNode pred;     // the predicate
  public Tool tool;             // null iff inVal is the real set
  public Context con;
  public TLCState state;
  public TLCState pstate;
  public int control;

  /* Constructor */
  public SetPredValue(Object vars, Value inVal, SemanticNode pred, Tool tool,
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

  public final byte getKind() { return SETPREDVALUE; }

  public final int compareTo(Object obj) {
    try {
      this.inVal = SetEnumValue.convert(this);
      this.tool = null;
      return this.inVal.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      this.inVal = SetEnumValue.convert(this);
      this.tool = null;
      return this.inVal.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(Value elem) {
    try {
      if (this.tool == null) {
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
            TupleValue tv = TupleValue.convert(elem);
            if ((tv != null) && (tv.elems.length == ids.length)) {
              Value[] vals = ((TupleValue)tv).elems;
              for (int i = 0; i < ids.length; i++) {
                con1 = con1.cons(ids[i], vals[i]);
              }
            }
            else {
              Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
              "\nis an element of a set of " + ids.length + "-tuples.");
            }
          }
          Value res = this.tool.eval(this.pred, con1, this.state, this.pstate, this.control);
          if (!(res instanceof BoolValue)) {
            Assert.fail("The evaluation of predicate " + this.pred +
                  " yielded non-Boolean value.");
          }
          return ((BoolValue)res).val;
        }
      }
      catch (EvalException e) {
        Assert.fail("Cannot decide if element:\n" + ppr(elem.toString()) +
        "\n is element of:\n" + ppr(this.inVal.toString()) +
        "\nand satisfies the predicate " + this.pred);
      }
      return false;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      if (!(this.inVal.isFinite())) {
        Assert.fail("Attempted to check if expression of form {x \\in S : p(x)} is a " +
        "finite set, but cannot check if S:\n" + ppr(this.inVal.toString()) +
        "\nis finite.");
      }
      return true;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT to the set " + ppr(this.toString()) + ".");
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT to the set " + ppr(this.toString()) + ".");
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      this.inVal = SetEnumValue.convert(this);
      this.tool = null;
      return this.inVal.size();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final void readObject(ObjectInputStream ois) throws IOException, ClassNotFoundException {
    this.inVal = (Value)ois.readObject();
    this.tool = null;
  }

  private final void writeObject(ObjectOutputStream oos) throws IOException {
    if (this.tool != null) {
      this.inVal = SetEnumValue.convert(this);
      this.tool = null;
    }
    oos.writeObject(this.inVal);
  }

  /* This method normalizes (destructively) this set. */
  public final boolean isNormalized() {
    try {
      return this.inVal.isNormalized();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final void normalize() {
    try {
      this.inVal.normalize();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    try {
      return this.equals(val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The fingerprint method */
  public final long fingerPrint(long fp) {
    try {
      this.inVal = SetEnumValue.convert(this);
      this.tool = null;
      return this.inVal.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value permute(MVPerm perm) {
    try {
      this.inVal = SetEnumValue.convert(this);
      this.tool = null;
      return this.inVal.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The string representation of the value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      try {
        if (expand) {
          Value val = SetEnumValue.convert(this);
          return val.toString(sb, offset);
        }
      }
      catch (Throwable e) { /*SKIP*/ }

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
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final ValueEnumeration elements() {
    try {
      if (this.tool == null) {
        return ((SetEnumValue)this.inVal).elements();
      }
      return new Enumerator();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  final class Enumerator implements ValueEnumeration {
    ValueEnumeration Enum;

    public Enumerator() {
      if (!(inVal instanceof Enumerable)) {
        Assert.fail("Attempted to enumerate { x \\in S : p(x) } when S:\n" +
              ppr(inVal.toString()) + "\nis not enumerable");
      }
      this.Enum = ((Enumerable)inVal).elements();
    }

    public final void reset() { this.Enum.reset(); }

    public final Value nextElement() {
      Value elem;
      while ((elem = this.Enum.nextElement()) != null) {
        Context con1 = con;
        if (vars instanceof FormalParamNode) {
          con1 = con1.cons((FormalParamNode)vars, elem);
        }
        else {
          FormalParamNode[] ids = (FormalParamNode[])vars;
          TupleValue tv = TupleValue.convert(elem);
          if ((tv != null) &&
              (((TupleValue)tv).elems.length == ids.length)) {
            Value[] vals = ((TupleValue)tv).elems;
            for (int i = 0; i < ids.length; i++) {
              con1 = con1.cons(ids[i], vals[i]);
            }
          }
          else {
            Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
            "\nis an element of a set of " + ids.length + "-tuples.");
          }
        }
        Value res = tool.eval(pred, con1, state, pstate, control);
        if (!(res instanceof BoolValue)) {
          Assert.fail("Evaluating predicate " + pred + " yielded non-Boolean value.");
        }
        if (((BoolValue)res).val) return elem;
      }
      return null;
    }

  }

}
