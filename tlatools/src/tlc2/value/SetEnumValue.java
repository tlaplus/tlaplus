// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:16:24 PST by lamport
//      modified on Mon Aug 20 10:54:08 PDT 2001 by yuanyu

package tlc2.value;

import java.io.IOException;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import util.Assert;

public class SetEnumValue extends EnumerableValue
implements Enumerable, Reducible {
  public ValueVec elems;         // the elements of the set
  private boolean isNorm;        // normalized?

  /* Constructor */
  public SetEnumValue(Value[] elems, boolean isNorm) {
	  this(new ValueVec(elems), isNorm);
  }

  public SetEnumValue(ValueVec elems, boolean isNorm) {
    this.elems = elems;
    this.isNorm = isNorm;
  }
  
  public SetEnumValue() {
	  this(new ValueVec(0), true);
  }

  public final byte getKind() { return SETENUMVALUE; }

  public final int compareTo(Object obj) {
    try {
      SetEnumValue set = obj instanceof Value ? ((Value)obj).toSetEnum() : null;
      if (set == null) {
        if (obj instanceof ModelValue) return 1;
        Assert.fail("Attempted to compare the set " + ppr(this.toString()) +
        " with the value:\n" + ppr(obj.toString()));
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
      SetEnumValue set = obj instanceof Value ? ((Value)obj).toSetEnum() : null;
      if (set == null) {
        if (obj instanceof ModelValue)
           return ((ModelValue) obj).modelValueEquals(this) ;
        Assert.fail("Attempted to check equality of the set " + ppr(this.toString()) +
        " with the value:\n" + ppr(obj.toString()));
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

  public final boolean member(Value elem) {
    try {
      return this.elems.search(elem, this.isNorm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() { return true; }

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
      return new SetEnumValue(diffElems, this.isNormalized());
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

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
      return new SetEnumValue(capElems, this.isNormalized());
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

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
      return new SetCupValue(this, set);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
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
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
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
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

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
  public final boolean isNormalized() { return this.isNorm; }

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
  public final SetEnumValue toSetEnum() {
	  return this;
  }

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

  public final Value deepCopy() { return this; }

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
	public final void write(ValueOutputStream vos) throws IOException {
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

  public final Value permute(MVPerm perm) {
    try {
      int sz = this.elems.size();
      Value[] vals = new Value[sz];
      boolean changed = false;
      for (int i = 0; i < sz; i++) {
        vals[i] = this.elems.elementAt(i).permute(perm);
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
  public final StringBuffer toString(StringBuffer sb, int offset) {
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
        this.elems.elementAt(0).toString(sb, offset);
      }
      for (int i = 1; i < len; i++) {
        sb.append(", ");
        this.elems.elementAt(i).toString(sb, offset);
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
     int index = (int) Math.floor(getRandom().nextDouble() * sz);
     return this.elems.elementAt(index);
  }

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

    public final void reset() { this.index = 0; }

    public final Value nextElement() {
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
    	return new SetEnumValue(vec, false);
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

	public static Value createFrom(final ValueInputStream vos) throws IOException {
		final int index = vos.getIndex();
		boolean isNorm = true;
		int len = vos.readInt();
		if (len < 0) {
			len = -len;
			isNorm = false;
		}
		final Value[] elems = new Value[len];
		for (int i = 0; i < len; i++) {
			elems[i] = vos.read();
		}
		final Value res = new SetEnumValue(elems, isNorm);
		vos.assign(res, index);
		return res;
	}
}
