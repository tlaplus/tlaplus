// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:16:24 PST by lamport
//      modified on Mon Aug 20 10:54:08 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;

import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.RandomEnumerableValues;
import tlc2.value.ValueInputStream;
import tlc2.value.Values;
import util.Assert;
import util.UniqueString;

@SuppressWarnings("serial")
public class SetEnumValue extends EnumerableValue
implements Enumerable, Reducible {
  public ValueVec elems;         // the elements of the set
  private boolean isNorm;        // normalized?
public static final SetEnumValue EmptySet = new SetEnumValue(new ValueVec(0), true);
public static final SetEnumValue DummyEnum = new SetEnumValue((ValueVec)null, true);

  /* Constructor */
  public SetEnumValue(Value[] elems, boolean isNorm) {
	  this(new ValueVec(elems), isNorm);
  }

  public SetEnumValue(Value[] vals, boolean isNorm, CostModel cm) {
	  this(vals, isNorm);
	  this.cm = cm;
  }

  public SetEnumValue(ValueVec elems, boolean isNorm) {
    this.elems = elems;
    this.isNorm = isNorm;
  }

  public SetEnumValue(ValueVec elems, boolean isNorm, final CostModel cm) {
	  this(elems, isNorm);
	  this.cm = cm;
  }

  public SetEnumValue() {
	  this(new ValueVec(0), true);
  }
  
  public SetEnumValue(final Value elem) {
	  this(new Value[] {elem}, true); // single element is normalized by definition.
  }
  
  public SetEnumValue(CostModel cm) {
	  this();
	  this.cm = cm;
  }
  
  // See IValue#isAtom except that this is for sets of atoms.
  public final boolean isSetOfAtoms() {
      final int len = this.elems.size();
      for (int i = 0; i < len; i++) {
    	  final Value v = this.elems.elementAt(i);
    	  if (v instanceof SetEnumValue) {
    		  // Sets of sets of sets... of atoms.
    		  final SetEnumValue sev = (SetEnumValue) v;
    		  if (!sev.isSetOfAtoms()) {
    			  return false;
    		  }
    	  } else if (!v.isAtom()) {
    		  return false;
    	  }
      }
      return true;
  }

  @Override
  public final byte getKind() { return SETENUMVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      SetEnumValue set = obj instanceof Value ? (SetEnumValue) ((Value)obj).toSetEnum() : null;
      if (set == null) {
        if (obj instanceof ModelValue) {
            return ((ModelValue) obj).modelValueCompareTo(this);
        }
        Assert.fail("Attempted to compare the set " + Values.ppr(this.toString()) +
        " with the value:\n" + Values.ppr(obj.toString()), getSource());
      }
      this.normalize();
      set.normalize();
      int sz = this.elems.size();
      int cmp = sz - set.elems.size();
      if (cmp != 0) return cmp;
      for (int i = 0; i < sz; i++) {
        cmp = this.elems.elementAt(i).compareTo(set.elems.elementAt(i));
        if (cmp != 0) return cmp;
      }
      return 0;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      SetEnumValue set = obj instanceof Value ? (SetEnumValue) ((Value)obj).toSetEnum() : null;
      if (set == null) {
        if (obj instanceof ModelValue)
           return ((ModelValue) obj).modelValueEquals(this) ;
        Assert.fail("Attempted to check equality of the set " + Values.ppr(this.toString()) +
        " with the value:\n" + Values.ppr(obj.toString()), getSource());
      }
      this.normalize();
      set.normalize();
      int sz = this.elems.size();
      if (sz != set.elems.size()) {
        return false;
      }
      for (int i = 0; i < sz; i++) {
        if (!this.elems.elementAt(i).equals(set.elems.elementAt(i))) {
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
  public final boolean member(Value elem) {
    try {
      return this.elems.search(elem, this.isNorm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() { return true; }

  @Override
  public final Value diff(Value val) {
    try {
      int sz = this.elems.size();
      ValueVec diffElems = new ValueVec();
      for (int i = 0; i < sz; i++) {
    	  Value elem = this.elems.elementAt(i);
        if (!val.member(elem)) {
          diffElems.addElement(elem);
        }
      }
      return new SetEnumValue(diffElems, this.isNormalized(), cm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value cap(Value val) {
    try {
      int sz = this.elems.size();
      ValueVec capElems = new ValueVec();
      for (int i = 0; i < sz; i++) {
    	  Value elem = this.elems.elementAt(i);
        if (val.member(elem)) {
          capElems.addElement(elem);
        }
      }
      return new SetEnumValue(capElems, this.isNormalized(), cm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value cup(Value set) {
    try {
      int sz = this.elems.size();
      if (sz == 0) return set;

      if (set instanceof Reducible) {
        ValueVec cupElems = new ValueVec();
        for (int i = 0; i < sz; i++) {
        	Value elem = this.elems.elementAt(i);
          cupElems.addElement(elem);
        }
        ValueEnumeration Enum = ((Enumerable)set).elements();
        Value elem;
        while ((elem = Enum.nextElement()) != null) {
          if (!this.member(elem)) cupElems.addElement(elem);
        }
        return new SetEnumValue(cupElems, false);
      }
      return new SetCupValue(this, set, cm);
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
      this.normalize();
      return this.elems.size();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This method normalizes (destructively) this set. */
  @Override
  public final boolean isNormalized() { return this.isNorm; }

  @Override
  public final Value normalize() {
    try {
      if (!this.isNorm) {
        this.elems.sort(true);   // duplicates eliminated
        this.isNorm = true;
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
      for (int i = 0; i < elems.size(); i++) {
          elems.elementAt(i).deepNormalize();
        }
        normalize();
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
  }

  @Override
  public final Value toSetEnum() {
	  return this;
  }
  
  // Unclear if overriding Value#toTuple would cause regressions (test suite
  // doesn't reveal one, but let's be safe.
  public final Value toTupleValue() {
	  // Remove duplicates.
	  this.normalize();
	  // Order of elements left undefined (implementation detail).
	  return new TupleValue(this.elems.toArray());
  }

  @Override
  public final boolean isDefined() {
    try {
      boolean defined = true;
      int sz = this.elems.size();
      for (int i = 0; i < sz; i++) {
        defined = defined && this.elems.elementAt(i).isDefined();
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

	@Override
	public final void write(IValueOutputStream vos) throws IOException {
		final int index = vos.put(this);
		if (index == -1) {
			vos.writeByte(SETENUMVALUE);
			final int len = elems.size();
			vos.writeInt((isNormalized()) ? len : -len);
			for (int i = 0; i < len; i++) {
				elems.elementAt(i).write(vos);
			}
		} else {
			vos.writeByte(DUMMYVALUE);
			vos.writeNat(index);
		}
	}

  /* The fingerprint methods */
  @Override
  public final long fingerPrint(long fp) {
    try {
      this.normalize();
      int sz = this.elems.size();
      fp = FP64.Extend(fp, SETENUMVALUE);
      fp = FP64.Extend(fp, sz);
      for (int i = 0; i < sz; i++) {
        Value elem = this.elems.elementAt(i);
        fp = elem.fingerPrint(fp);
      }
      return fp;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) {
    try {
      int sz = this.elems.size();
      Value[] vals = new Value[sz];
      boolean changed = false;
      for (int i = 0; i < sz; i++) {
        vals[i] = (Value) this.elems.elementAt(i).permute(perm);
        changed = (changed || vals[i] != this.elems.elementAt(i));
      }
      if (changed) {
        return new SetEnumValue(vals, false);
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The string representation */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      // If this SetEnumValue object is created by a union, at least one of
      // whose elements is a Cartesian product, then this can be an unnormalized
      // set with repeated elements.  It would therefore seem like a good idea to
      // normalize this object here.  Since this toString method is probably
      // used only for printing the value, it seems that correcting this should
      // not do any harm.  Therefore, LL added the following if statement
      // on 5 Mar 2012.
      // Beware:
      // normalize() mutates a SetEnumValue's state. Thus calling toString() 
      // on a SetEnumValue mutates its state. By convention, toString methods
      // generally do not mutate an instance's state (side-effect free) and
      // and are thus safe to be called. Failing to adhere to this convention
      // can lead to subtle bugs. E.g. think of a programmer who inspects an
      // instance with a debugger unconsciously mutating the instance's state.
      if (!this.isNormalized()) {
          this.normalize();
      }

      int len = this.elems.size();
      sb = sb.append("{");
      if (len > 0) {
        this.elems.elementAt(0).toString(sb, offset, swallow);
      }
      for (int i = 1; i < len; i++) {
        sb.append(", ");
        this.elems.elementAt(i).toString(sb, offset, swallow);
      }
      sb.append("}");
      return sb;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value randomElement() {
     int sz = size();
     int index = (int) Math.floor(RandomEnumerableValues.get().nextDouble() * sz);
     return this.elems.elementAt(index);
  }

  @Override
  public final ValueEnumeration elements() {
    try {
      return new Enumerator();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  final class Enumerator implements ValueEnumeration {
    int index = 0;

    public Enumerator() {
    	normalize();
    }

    @Override
    public final void reset() { this.index = 0; }

    @Override
    public final Value nextElement() {
    	if (coverage) { cm.incSecondary(); }
      if (this.index < elems.size()) {
        return elems.elementAt(this.index++);
      }
      return null;
    }
  }

    @Override
	public EnumerableValue getRandomSubset(final int kOutOfN) {
    	final ValueVec vec = new ValueVec(kOutOfN);
    	
    	final ValueEnumeration ve = elements(kOutOfN);
    	
    	Value v = null;
    	while ((v = ve.nextElement()) != null) {
    		vec.addElement(v);
    	}
    	return new SetEnumValue(vec, false, cm);
	}

	@Override
	public ValueEnumeration elements(Ordering ordering) {
		if (ordering == Ordering.RANDOMIZED) {
			return elements(size());
		}
		return super.elements(ordering);
	}

	@Override
	public ValueEnumeration elements(final int k) {
		normalize();
		return new EnumerableValue.SubsetEnumerator(k) {
			@Override
			public Value nextElement() {
				if (!hasNext()) {
					return null;
				}
				return elems.elementAt(nextIndex());
			}
		};
	}

	public static IValue createFrom(final IValueInputStream vos) throws IOException {
		final int index = vos.getIndex();
		boolean isNorm = true;
		int len = vos.readInt();
		if (len < 0) {
			len = -len;
			isNorm = false;
		}
		final Value[] elems = new Value[len];
		for (int i = 0; i < len; i++) {
			elems[i] = (Value) vos.read();
		}
		final Value res = new SetEnumValue(elems, isNorm);
		vos.assign(res, index);
		return res;
	}

	public static IValue createFrom(final ValueInputStream vos, final Map<String, UniqueString> tbl) throws IOException {
		final int index = vos.getIndex();
		boolean isNorm = true;
		int len = vos.readInt();
		if (len < 0) {
			len = -len;
			isNorm = false;
		}
		final Value[] elems = new Value[len];
		for (int i = 0; i < len; i++) {
			elems[i] = (Value) vos.read(tbl);
		}
		final Value res = new SetEnumValue(elems, isNorm);
		vos.assign(res, index);
		return res;
	}

	@Override
	public List<TLCVariable> getTLCVariables(final TLCVariable prototype, Random rnd) {
		final List<TLCVariable> nestedVars = new ArrayList<>(this.size());
		ValueEnumeration elements = this.elements();
		Value value;
		while ((value = elements.nextElement()) != null) {
			final TLCVariable nested = prototype.newInstance(value.toString(), value, rnd);
			nested.setName(value.toString());
			nested.setValue(value.toString());
			nestedVars.add(nested);
		}
		return nestedVars;
	}
}
