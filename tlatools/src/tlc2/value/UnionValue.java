// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:46:50 PST by lamport
//      modified on Fri Aug 10 15:10:39 PDT 2001 by yuanyu

package tlc2.value;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import util.Assert;

public class UnionValue extends EnumerableValue implements Enumerable {
  public final IValue set;
  protected SetEnumValue realSet;

  /* Constructor */
  public UnionValue(IValue set) {
    this.set = set;
    this.realSet = null;
  }

  public UnionValue(IValue val, CostModel cm) {
	  this(val);
	  this.cm = cm;
  }

  public byte getKind() { return UNIONVALUE; }

  public final int compareTo(Object obj) {
    try {
      this.convertAndCache();
      return this.realSet.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      this.convertAndCache();
      return this.realSet.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(IValue elem) {
    try {
      if (!(this.set instanceof Enumerable)) {
        Assert.fail("Attempted to check if:\n " + Values.ppr(elem.toString()) +
        "\nis an element of the non-enumerable set:\n " +
        Values.ppr(this.toString()));
      }
      ValueEnumeration Enum = ((Enumerable)this.set).elements();
      IValue val;
      while ((val = Enum.nextElement()) != null) {
        if (val.member(elem)) return true;
      }
      return false;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      if (!(this.set instanceof Enumerable)) {
        Assert.fail("Attempted to check if the nonenumerable set:\n" + Values.ppr(this.toString()) +
        "\nis a finite set.");
      }
      ValueEnumeration Enum = ((Enumerable)this.set).elements();
      IValue val;
      while ((val = Enum.nextElement()) != null) {
        if (!val.isFinite()) return false;
      }
      return true;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT to the set:\n" + Values.ppr(this.toString()));
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT to the set:\n " + Values.ppr(this.toString()) + ".");
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      this.convertAndCache();
      return this.realSet.size();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isNormalized() {
    try {
      return (this.realSet != null &&
        this.realSet != DummyEnum &&
        this.realSet.isNormalized());
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue normalize() {
    try {
      if (this.realSet != null && this.realSet != DummyEnum) {
        this.realSet.normalize();
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
      if (realSet == null) {
        realSet = DummyEnum;
      }
      else if (realSet != DummyEnum) {
        realSet.deepNormalize();
      }
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
  }

  public final boolean isDefined() {
    try {
      return this.set.isDefined();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue deepCopy() { return this; }

  public final boolean assignable(IValue val) {
    try {
      return this.equals(val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public static IValue union(IValue val) {
    boolean canCombine = (val instanceof SetEnumValue);
    if (canCombine) {
      ValueVec elems = ((SetEnumValue)val).elems;
      for (int i = 0; i < elems.size(); i++) {
        canCombine = (canCombine &&
                (elems.elementAt(i) instanceof SetEnumValue));
      }
      if (canCombine) {
        ValueVec resElems = new ValueVec();
        IValue result = new SetEnumValue(resElems, false, val.getCostModel());
        for (int i = 0; i < elems.size(); i++) {
          ValueVec elems1 = ((SetEnumValue)elems.elementAt(i)).elems;
          for (int j = 0; j < elems1.size(); j++) {
        	  IValue elem = elems1.elementAt(j);
            if (!result.member(elem)) {
            	resElems.addElement(elem);
            }
          }
        }
        return result;
      }
    }
    return new UnionValue(val, val.getCostModel());
  }

	@Override
	public void write(final ValueOutputStream vos) throws IOException {
		realSet.write(vos);
	}

  /* The fingerprint  */
  public final long fingerPrint(long fp) {
    try {
      this.convertAndCache();
      return this.realSet.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue permute(MVPerm perm) {
    try {
      this.convertAndCache();
      return this.realSet.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final void convertAndCache() {
    if (this.realSet == null) {
      this.realSet = (SetEnumValue) this.toSetEnum();
    }
    else if (this.realSet == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
        if (this.realSet == DummyEnum) {
          val = (SetEnumValue) this.toSetEnum();
          val.deepNormalize();
        }
      }
      synchronized(this) {
        if (this.realSet == DummyEnum) { this.realSet = val; }
      }
    }
  }

  @Override
  public final IValue toSetEnum() {
      if (this.realSet != null && this.realSet != DummyEnum) {
        return this.realSet;
      }
      ValueVec vals = new ValueVec();
      ValueEnumeration Enum = this.elements();
      IValue elem;
      while ((elem = Enum.nextElement()) != null) {
        vals.addElement(elem);
      }
      if (coverage) {cm.incSecondary(vals.size());}
      return new SetEnumValue(vals, false, cm);
  }

  /* String representation of this value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      if (TLCGlobals.expand) {
        IValue val = this.toSetEnum();
        return val.toString(sb, offset);
      }
      else {
        sb = sb.append("UNION(");
        sb = this.set.toString(sb, offset);
        sb.append(")");
        return sb;
      }
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final ValueEnumeration elements() {
    try {
      if (this.realSet == null || this.realSet == DummyEnum) {
        return new Enumerator();
      }
      return this.realSet.elements();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  final class Enumerator implements ValueEnumeration {
    ValueEnumeration Enum;
    IValue elemSet;
    ValueEnumeration elemSetEnum;

    public Enumerator() {
      if (!(set instanceof Enumerable)) {
        Assert.fail("Attempted to enumerate the nonenumerable set:\n"+
              Values.ppr(this.toString()));
      }
      this.Enum = ((Enumerable)set).elements();
      this.elemSet = this.Enum.nextElement();
      if (this.elemSet != null) {
        if (!(this.elemSet instanceof Enumerable)) {
          Assert.fail("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
        }
        this.elemSetEnum = ((Enumerable)this.elemSet).elements();
      }
    }

    public final void reset() {
      this.Enum.reset();
      this.elemSet = this.Enum.nextElement();
      this.elemSetEnum = ((Enumerable)this.elemSet).elements();
    }

    public final IValue nextElement() {
      if (this.elemSet == null) return null;
      IValue val = this.elemSetEnum.nextElement();
      if (val == null) {
        this.elemSet = this.Enum.nextElement();
        if (this.elemSet == null) return null;
        if (!(this.elemSet instanceof Enumerable)) {
          Assert.fail("Attempted to enumerate the nonenumerable set:\n" +
                Values.ppr(this.elemSet.toString()) +
                "\nwhen enumerating:\n" + Values.ppr(this.toString()));
        }
        this.elemSetEnum = ((Enumerable)this.elemSet).elements();
        val = this.nextElement();
      }
	  if (coverage) { cm.incSecondary(); }
      return val;
    }

  }

}
