// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2021, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:18:39 PST by lamport
//      modified on Fri Aug 10 15:09:59 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

public class SetOfTuplesValue extends EnumerableValue implements Enumerable {
  public final Value[] sets;
  protected SetEnumValue tupleSet;

  /* Constructor */
  public SetOfTuplesValue(Value[] sets) {
    this.sets = sets;
    this.tupleSet = null;
  }
  public SetOfTuplesValue(Value[] set, CostModel cm) {
	  this(set);
	  this.cm = cm;
  }

  public SetOfTuplesValue(Value val) {
	  this(new Value[1]);
    this.sets[0] = val;
  }

  public SetOfTuplesValue(Value v1, Value v2) {
	  this(new Value[2]);
    this.sets[0] = v1;
    this.sets[1] = v2;
  }

  @Override
  public final byte getKind() { return SETOFTUPLESVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      this.convertAndCache();
      return this.tupleSet.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      if (obj instanceof SetOfTuplesValue) {
        SetOfTuplesValue tvs = (SetOfTuplesValue)obj;

        boolean isEmpty1 = this.isEmpty();
        if (isEmpty1) return tvs.isEmpty();
        if (tvs.isEmpty()) return isEmpty1;

        if (this.sets.length != tvs.sets.length) {
          return false;
        }
        for (int i = 0; i < this.sets.length; i++) {
          if (!this.sets[i].equals(tvs.sets[i])) {
            return false;
          }
        }
        return true;
      }
      this.convertAndCache();
      return this.tupleSet.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean member(Value elem) {
    try {
      TupleValue tv = (TupleValue) elem.toTuple();
      if (tv == null) {
        FcnRcdValue fcn = (FcnRcdValue) elem.toFcnRcd();
        if (fcn == null) {
          if (elem instanceof ModelValue)
            return ((ModelValue) elem).modelValueMember(this) ;
          Assert.fail("Attempted to check if non-tuple\n" + Values.ppr(elem.toString()) +
                "\nis in the set of tuples:\n" + Values.ppr(this.toString()), getSource());
        }
        if (fcn.intv != null) return false;
        for (int i = 0; i < fcn.domain.length; i++) {
          if (!(fcn.domain[i] instanceof IntValue)) {
            Assert.fail("Attempted to check if non-tuple\n" + Values.ppr(elem.toString()) +
                  "\nis in the set of tuples:\n" + Values.ppr(this.toString()), getSource());
          }
        }
        return false;
      }
      if (tv.elems.length == this.sets.length) {
        for (int i = 0; i < this.sets.length; i++) {
          if (!this.sets[i].member(tv.elems[i]))
            return false;
        }
        return true;
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
      for (int i = 0; i < this.sets.length; i++) {
        if (!this.sets[i].isFinite()) {
          return false;
        }
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
        Assert.fail("Attempted to apply EXCEPT construct to the set of tuples:\n" +
        Values.ppr(this.toString()), getSource());
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
        Assert.fail("Attempted to apply EXCEPT construct to the set of tuples:\n" +
        Values.ppr(this.toString()), getSource());
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
      long sz = 1;
      for (int i = 0; i < this.sets.length; i++) {
        sz *= this.sets[i].size();
        if (sz < -2147483648 || sz > 2147483647) {
          Assert.fail("Overflow when computing the number of elements in " +
                Values.ppr(this.toString()), getSource());
        }
      }
      return (int)sz;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isNormalized() {
    try {
      if (this.tupleSet == null || this.tupleSet == SetEnumValue.DummyEnum) {
        for (int i = 0; i < this.sets.length; i++) {
          if (!this.sets[i].isNormalized()) {
            return false;
          }
        }
        return true;
      }
      return this.tupleSet.isNormalized();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value normalize() {
    try {
      if (this.tupleSet == null || this.tupleSet == SetEnumValue.DummyEnum) {
        for (int i = 0; i < this.sets.length; i++) {
          this.sets[i].normalize();
        }
      }
      else {
        this.tupleSet.normalize();
      }
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
      for (int i = 0; i < sets.length; i++) {
          sets[i].deepNormalize();
        }
        if (tupleSet == null) {
          tupleSet = SetEnumValue.DummyEnum;
        }
        else if (tupleSet != SetEnumValue.DummyEnum) {
          tupleSet.deepNormalize();
        }
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
      for (int i = 0; i < this.sets.length; i++) {
        defined = defined && this.sets[i].isDefined();
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
      return this.equals(val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The fingerprint  */
  @Override
  public final long fingerPrint(long fp) {
    try {
      this.convertAndCache();
      return this.tupleSet.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) {
    try {
      this.convertAndCache();
      return this.tupleSet.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final void convertAndCache() {
    if (this.tupleSet == null) {
      this.tupleSet = (SetEnumValue) this.toSetEnum();
    }
    else if (this.tupleSet == SetEnumValue.DummyEnum) {
      SetEnumValue val = (SetEnumValue) this.toSetEnum();
      val.deepNormalize();
      this.tupleSet = val;
    }
  }

  @Override
  public final Value toSetEnum() {
      if (this.tupleSet != null && this.tupleSet != SetEnumValue.DummyEnum) {
        return this.tupleSet;
      }
      ValueVec vals = new ValueVec();
      ValueEnumeration Enum = this.elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
        vals.addElement(elem);
      }
      if (coverage) {cm.incSecondary(vals.size());}
      return new SetEnumValue(vals, this.isNormalized(), cm);
  }

  @Override
  public final void write(final IValueOutputStream vos) throws IOException {
	  tupleSet.write(vos);
  }

  /* The string representation of the value. */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      boolean unlazy = TLCGlobals.expand;
      try {
        if (unlazy) {
          long sz = 1;
          for (int i = 0; i < this.sets.length; i++) {
            sz *= this.sets[i].size();
            if (sz < -2147483648 || sz > 2147483647) {
              unlazy = false;
              break;
            }
          }
          unlazy = sz < TLCGlobals.enumBound;
        }
      }
      catch (Throwable e) { if (swallow) unlazy = false; else throw e; }

      if (unlazy) {
        Value val = this.toSetEnum();
        return val.toString(sb, offset, swallow);
      }
      else {
        if (this.sets.length > 0) {
          sb.append("(");
          this.sets[0].toString(sb, offset, swallow);
        }
        for (int i = 1; i < this.sets.length; i++) {
          sb.append(" \\X ");
          this.sets[i].toString(sb, offset, swallow);
        }
        if (this.sets.length > 0) {
          sb.append(")");
        }
        return sb;
      }
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final ValueEnumeration elements() {
    try {
      if (this.tupleSet == null || this.tupleSet == SetEnumValue.DummyEnum) {
        return new Enumerator();
      }
      return this.tupleSet.elements();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  final class Enumerator implements ValueEnumeration {
    private ValueEnumeration[] enums;
    private Value[] currentElems;
    private boolean isDone;

    public Enumerator() {
      this.enums = new ValueEnumeration[sets.length];
      this.currentElems = new Value[sets.length];
      this.isDone = false;
      for (int i = 0; i < sets.length; i++) {
        if (sets[i] instanceof Enumerable) {
          this.enums[i] = ((Enumerable)sets[i]).elements();
          this.currentElems[i] = this.enums[i].nextElement();
          if (this.currentElems[i] == null) {
            this.enums = null;
            this.isDone = true;
            break;
          }
        }
        else {
          Assert.fail("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn," +
                "\nbut can't enumerate s" + i + ":\n" + Values.ppr(sets[i].toString()), getSource());
        }
      }
    }

    @Override
    public final void reset() {
      if (this.enums != null) {
        for (int i = 0; i < this.enums.length; i++) {
          this.enums[i].reset();
          this.currentElems[i] = this.enums[i].nextElement();
        }
        this.isDone = false;
      }
    }

    @Override
    public final Value nextElement() {
      if (this.isDone) return null;
      Value[] elems = new Value[this.currentElems.length];
	  if (coverage) { cm.incSecondary(elems.length); }
      for (int i = 0; i < elems.length; i++) {
        elems[i] = this.currentElems[i];
      }
      for (int i = elems.length-1; i >= 0; i--) {
        this.currentElems[i] = this.enums[i].nextElement();
        if (this.currentElems[i] != null) break;
        if (i == 0) {
          this.isDone = true;
          break;
        }
        this.enums[i].reset();
        this.currentElems[i] = this.enums[i].nextElement();
      }
      return new TupleValue(elems, cm);
    }
  }

}
