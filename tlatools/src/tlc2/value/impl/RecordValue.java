// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:15:47 PST by lamport
//      modified on Fri Aug 10 15:09:07 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.EOFException;
import java.io.IOException;
import java.util.Arrays;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;
import util.UniqueString;

public class RecordValue extends Value implements Applicable {
  public final UniqueString[] names;   // the field names
  public final Value[] values;         // the field values
  private boolean isNorm;
public final static RecordValue EmptyRcd = new RecordValue(new UniqueString[0], new Value[0], true);

  /* Constructor */
  public RecordValue(UniqueString[] names, Value[] values, boolean isNorm) {
    this.names = names;
    this.values = values;
    this.isNorm = isNorm;
  }

  public RecordValue(UniqueString[] names, Value[] values, boolean isNorm, CostModel cm) {
	  this(names, values, isNorm);
	  this.cm = cm;
  }

  @Override
  public final byte getKind() { return RECORDVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      RecordValue rcd = obj instanceof Value ? (RecordValue) ((Value)obj).toRcd() : null;
      if (rcd == null) {
        if (obj instanceof ModelValue) return 1;
        Assert.fail("Attempted to compare record:\n" + Values.ppr(this.toString()) +
        "\nwith non-record\n" + Values.ppr(obj.toString()));
      }
      this.normalize();
      rcd.normalize();
      int len = this.names.length;
      int cmp = len - rcd.names.length;
      if (cmp == 0) {
        for (int i = 0; i < len; i++) {
          cmp = this.names[i].compareTo(rcd.names[i]);
          if (cmp != 0) break;
          cmp = this.values[i].compareTo(rcd.values[i]);
          if (cmp != 0) break;
        }
      }
      return cmp;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      RecordValue rcd = obj instanceof Value ? (RecordValue) ((Value)obj).toRcd() : null;
      if (rcd == null) {
        if (obj instanceof ModelValue)
           return ((ModelValue) obj).modelValueEquals(this) ;
        Assert.fail("Attempted to check equality of record:\n" + Values.ppr(this.toString()) +
        "\nwith non-record\n" + Values.ppr(obj.toString()));
      }
      this.normalize();
      rcd.normalize();
      int len = this.names.length;
      if (len != rcd.names.length) return false;
      for (int i = 0; i < len; i++) {
        if ((!(this.names[i].equals(rcd.names[i]))) ||
          (!(this.values[i].equals(rcd.values[i]))))
          return false;
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
      Assert.fail("Attempted to check if element:\n" + Values.ppr(elem.toString()) +
                  "\nis in the record:\n" + Values.ppr(this.toString()));
      return false;    // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() { return true; }

  @Override
  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        int rlen = this.names.length;
        Value[] newValues = new Value[rlen];
        Value arcVal = ex.path[ex.idx];
        if (arcVal instanceof StringValue) {
          UniqueString arc = ((StringValue)arcVal).val;
          for (int i = 0; i < rlen; i++) {
            if (this.names[i].equals(arc)) {
              ex.idx++;
              newValues[i] = this.values[i].takeExcept(ex);
            }
            else {
              newValues[i] = this.values[i];
            }
          }
          UniqueString[] newNames = this.names;
          if (!this.isNorm) {
            newNames = new UniqueString[rlen];
            for (int i = 0; i < rlen; i++) {
              newNames[i] = this.names[i];
            }
          }
          return new RecordValue(newNames, newValues, this.isNorm);
        }
        else {
            MP.printWarning(EC.TLC_WRONG_RECORD_FIELD_NAME, new String[]{Values.ppr(arcVal.toString())});
        }
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
      Value res = this;
      for (int i = 0; i < exs.length; i++) {
        res = res.takeExcept(exs[i]);
      }
      return res;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value toRcd() {
	  return this;
  }
  
  @Override
  public final Value toTuple() {
	  return size() == 0 ? TupleValue.EmptyTuple : super.toTuple();
  }

  @Override
	public final Value toFcnRcd() {
        this.normalize();
        Value[] dom = new Value[this.names.length];
        for (int i = 0; i < this.names.length; i++) {
          dom[i] = new StringValue(this.names[i], cm);
        }
        if (coverage) {cm.incSecondary(dom.length);}
        return new FcnRcdValue(dom, this.values, this.isNormalized(), cm);
	}

  @Override
  public final int size() {
    try {
      return this.names.length;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value apply(Value arg, int control) {
    try {
      if (!(arg instanceof StringValue)) {
        Assert.fail("Attempted to apply record to a non-string value " +
        Values.ppr(arg.toString()) + ".");
      }
      UniqueString name = ((StringValue)arg).getVal();
      int rlen = this.names.length;
      for (int i = 0; i < rlen; i++) {
        if (name.equals(this.names[i])) {
          return this.values[i];
        }
      }
      Assert.fail("Attempted to apply the record\n" + Values.ppr(this.toString()) +
      "\nto nonexistent record field " + name + ".");
      return null;    // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value apply(Value[] args, int control) {
    try {
      if (args.length != 1) {
        Assert.fail("Attempted to apply record to more than one arguments.");
      }
      return this.apply(args[0], control);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This method returns the named component of the record. */
  @Override
  public final Value select(Value arg) {
    try {
      if (!(arg instanceof StringValue)) {
        Assert.fail("Attempted to apply record to a non-string argument " +
        Values.ppr(arg.toString()) + ".");
      }
      UniqueString name = ((StringValue)arg).getVal();
      int rlen = this.names.length;
      for (int i = 0; i < rlen; i++) {
        if (name.equals(this.names[i])) {
          return this.values[i];
        }
      }
      return null;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value getDomain() {
    try {
    	Value[] dElems = new Value[this.names.length];
      for (int i = 0; i < this.names.length; i++) {
        dElems[i] = new StringValue(this.names[i]);
      }
      return new SetEnumValue(dElems, this.isNormalized());
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean assign(UniqueString name, Value val) {
    try {
      for (int i = 0; i < this.names.length; i++) {
        if (name.equals(this.names[i])) {
          if (this.values[i] == UndefValue.ValUndef ||
              this.values[i].equals(val)) {
            this.values[i] = val;
            return true;
          }
          return false;
        }
      }
      Assert.fail("Attempted to assign to nonexistent record field " + name + ".");
      return false;    // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isNormalized() { return this.isNorm; }

  @Override
  public final Value normalize() {
    try {
      if (!this.isNorm) {
        int len = this.names.length;
        for (int i = 1; i < len; i++) {
          int cmp = this.names[0].compareTo(this.names[i]);
          if (cmp == 0) {
            Assert.fail("Field name " + this.names[i] + " occurs multiple times in record.");
          }
          else if (cmp > 0) {
            UniqueString ts = this.names[0];
            this.names[0] = this.names[i];
            this.names[i] = ts;
            Value tv = this.values[0];
            this.values[0] = this.values[i];
            this.values[i] = tv;
          }
        }
        for (int i = 2; i < len; i++) {
          int j = i;
          UniqueString st = this.names[i];
          Value val = this.values[i];
          int cmp;
          while ((cmp = st.compareTo(this.names[j-1])) < 0) {
            this.names[j] = this.names[j-1];
            this.values[j] = this.values[j-1];
            j--;
          }
          if (cmp == 0) {
            Assert.fail("Field name " + this.names[i] + " occurs multiple times in record.");
          }
          this.names[j] = st;
          this.values[j] = val;
        }
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
      for (int i = 0; i < values.length; i++) {
          values[i].deepNormalize();
        }
        normalize();
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
      for (int i = 0; i < this.values.length; i++) {
        defined = defined && this.values[i].isDefined();
      }
      return defined;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue deepCopy() {
    try {
    	Value[] vals = new Value[this.values.length];
      for (int i = 0; i < this.values.length; i++) {
        vals[i] = (Value) this.values[i].deepCopy();
      }
      // Following code modified 16 June 2015 by adding Arrays.copyOf to fix
      // the following bug that seems to have manifested itself only in TLC.Print and
      // TLC.PrintT: Calling normalize on the original modifies the
      // order of the names array in the deepCopy (and vice-versa) without doing the
      // corresponding modification on the values array. Thus, the names are
      // copied too to prevent any modification/normalization done to the
      // original to appear in the deepCopy.
      return new RecordValue(Arrays.copyOf(this.names, this.names.length), vals, this.isNorm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean assignable(Value val) {
    try {
      boolean canAssign = ((val instanceof RecordValue) &&
        this.names.length == ((RecordValue)val).names.length);
      if (!canAssign) return false;
      for (int i = 0; i < this.values.length; i++) {
        canAssign = (canAssign &&
         this.names[i].equals(((RecordValue)val).names[i]) &&
         this.values[i].assignable(((RecordValue)val).values[i]));
      }
      return canAssign;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public final void write(final IValueOutputStream vos) throws IOException {
		final int index = vos.put(this);
		if (index == -1) {
			vos.writeByte(RECORDVALUE);
			final int len = names.length;
			vos.writeInt((isNormalized()) ? len : -len);
			for (int i = 0; i < len; i++) {
				final int index1 = vos.put(names[i]);
				if (index1 == -1) {
					vos.writeByte(STRINGVALUE);
					names[i].write(vos.getOutputStream());
				} else {
					vos.writeByte(DUMMYVALUE);
					vos.writeNat(index1);
				}
				values[i].write(vos);
			}
		} else {
			vos.writeByte(DUMMYVALUE);
			vos.writeNat(index);
		}
	}

  /* The fingerprint methods.  */
  @Override
  public final long fingerPrint(long fp) {
    try {
      this.normalize();
      int rlen = this.names.length;
      fp = FP64.Extend(fp, FCNRCDVALUE);
      fp = FP64.Extend(fp, rlen);
      for (int i = 0; i < rlen; i++) {
        String str = this.names[i].toString();
        fp = FP64.Extend(fp, STRINGVALUE);
        fp = FP64.Extend(fp, str.length());
        fp = FP64.Extend(fp, str);
        fp = this.values[i].fingerPrint(fp);
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
      this.normalize();
      int rlen = this.names.length;
      Value[] vals = new Value[rlen];
      boolean changed = false;
      for (int i = 0; i < rlen; i++) {
        vals[i] = (Value) this.values[i].permute(perm);
        changed = changed || (vals[i] != this.values[i]);
      }
      if (changed) {
        return new RecordValue(this.names, vals, true);
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
      int len = this.names.length;

      sb.append("[");
      if (len > 0) {
        sb.append(this.names[0] + " |-> ");
        sb = this.values[0].toString(sb, offset, swallow);
      }
      for (int i = 1; i < len; i++) {
        sb.append(", ");
        sb.append(this.names[i] + " |-> ");
        sb = this.values[i].toString(sb, offset, swallow);
      }
      return sb.append("]");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	public static IValue createFrom(final IValueInputStream vos) throws EOFException, IOException {
		final int index = vos.getIndex();
		boolean isNorm = true;
		int len = vos.readInt();
		if (len < 0) {
			len = -len;
			isNorm = false;
		}
		final UniqueString[] names = new UniqueString[len];
		final Value[] vals = new Value[len];
		for (int i = 0; i < len; i++) {
			final byte kind1 = vos.readByte();
			if (kind1 == DUMMYVALUE) {
				final int index1 = vos.readNat();
				names[i] = vos.getValue(index1);
			} else {
				final int index1 = vos.getIndex();
				names[i] = UniqueString.read(vos.getInputStream());
				vos.assign(names[i], index1);
			}
			vals[i] = (Value) vos.read();
		}
		final Value res = new RecordValue(names, vals, isNorm);
		vos.assign(res, index);
		return res;
	}
}
