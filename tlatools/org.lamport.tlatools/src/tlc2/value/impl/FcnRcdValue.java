// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:07:06 PST by lamport
//      modified on Fri Aug 10 15:07:25 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.util.Map;

import tlc2.tool.EvalControl;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.IFcnRcdValue;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.ValueInputStream;
import tlc2.value.Values;
import util.Assert;
import util.TLAConstants;
import util.UniqueString;

public class FcnRcdValue extends Value implements Applicable, IFcnRcdValue {
  public final Value[] domain;
  public final IntervalValue intv;
  public final Value[] values;
  private boolean isNorm;
  public static final Value EmptyFcn = new FcnRcdValue(new Value[0], new Value[0], true);

  /* Constructor */
  public FcnRcdValue(Value[] domain, Value[] values, boolean isNorm) {
    this.domain = domain;
    this.values = values;
    this.intv = null;
    this.isNorm = isNorm;
  }

  public FcnRcdValue(IntervalValue intv, Value[] values) {
    this.intv = intv;
    this.values = values;
    this.domain = null;
    this.isNorm = true;
  }

  public FcnRcdValue(IntervalValue intv, Value[] values, CostModel cm) {
	  this(intv, values);
	  this.cm = cm;
  }

  private FcnRcdValue(FcnRcdValue fcn, Value[] values) {
    this.domain = fcn.domain;
    this.intv = fcn.intv;
    this.values = values;
    this.isNorm = fcn.isNorm;
  }

  public FcnRcdValue(ValueVec elems, Value[] values, boolean isNorm) {
	  this(elems.toArray(), values, isNorm);
  }

  public FcnRcdValue(ValueVec elems, Value[] values, boolean isNorm, CostModel cm) {
	  this(elems, values, isNorm);
	  this.cm = cm;
  }

  public FcnRcdValue(Value[] domain, Value[] values, boolean isNorm, CostModel cm) {
	  this(domain, values, isNorm);
	  this.cm = cm;
  }

  @Override
  public final byte getKind() { return FCNRCDVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {

			final FcnRcdValue fcn = obj instanceof Value ? (FcnRcdValue) ((Value) obj).toFcnRcd() : null;
			if (fcn == null) {
				if (obj instanceof ModelValue)
					return 1;
				Assert.fail("Attempted to compare the function " + Values.ppr(this.toString()) + " with the value:\n"
						+ Values.ppr(obj.toString()));
			}
			this.normalize();
			fcn.normalize();

			final int result = this.values.length - fcn.values.length;
			if (result != 0) {
				return result;
			}

			if (this.intv != null) {
				return compareToInterval(fcn);
			} else {
				return compareOtherInterval(fcn);
			}

    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final int compareOtherInterval(final FcnRcdValue fcn) {
	int result;
	if (fcn.intv != null) {
		for (int i = 0; i < this.domain.length; i++) {
			final Value dElem = this.domain[i];
			if (!(dElem instanceof IntValue)) {
				Assert.fail(
						"Attempted to compare integer with non-integer\n" + Values.ppr(dElem.toString()) + ".");
			}
			result = ((IntValue) dElem).val - (fcn.intv.low + i);
			if (result != 0) {
				return result;
			}
			result = this.values[i].compareTo(fcn.values[i]);
			if (result != 0) {
				return result;
			}
		}
	} else {
		for (int i = 0; i < this.domain.length; i++) {
			result = this.domain[i].compareTo(fcn.domain[i]);
			if (result != 0) {
				return result;
			}
			result = this.values[i].compareTo(fcn.values[i]);
			if (result != 0) {
				return result;
			}
		}
	}
	return 0;
  }

  private final int compareToInterval(final FcnRcdValue fcn) {
  	int result;
  	if (fcn.intv != null) {
  		result = this.intv.low - fcn.intv.low;
  		if (result != 0) {
  			return result;
  		}
  		for (int i = 0; i < this.values.length; i++) {
  			result = this.values[i].compareTo(fcn.values[i]);
  			if (result != 0) {
  				return result;
  			}
  		}
  	} else {
  		for (int i = 0; i < fcn.domain.length; i++) {
  			final Value dElem = fcn.domain[i];
  			if (!(dElem instanceof IntValue)) {
  				Assert.fail(
  						"Attempted to compare integer with non-integer:\n" + Values.ppr(dElem.toString()) + ".");
  			}
  			result = this.intv.low + i - ((IntValue) dElem).val;
  			if (result != 0) {
  				return result;
  			}
  			result = this.values[i].compareTo(fcn.values[i]);
  			if (result != 0) {
  				return result;
  			}
  		}
  	}
  	return 0;
  }
  
  public final boolean equals(Object obj) {
    try {

      FcnRcdValue fcn = obj instanceof Value ? (FcnRcdValue) ((Value)obj).toFcnRcd() : null;
      if (fcn == null) {
        if (obj instanceof ModelValue)
           return ((ModelValue) obj).modelValueEquals(this) ;
        Assert.fail("Attempted to check equality of the function " + Values.ppr(this.toString()) +
        " with the value:\n" + Values.ppr(obj.toString()));
      }
      this.normalize();
      fcn.normalize();

      if (this.intv != null) {
        if (fcn.intv != null) {
          if (!this.intv.equals(fcn.intv)) return false;
          for (int i = 0; i < this.values.length; i++) {
            if (!this.values[i].equals(fcn.values[i]))
              return false;
          }
        }
        else {
          if (fcn.domain.length != this.intv.size()) return false;
          for (int i = 0; i < fcn.domain.length; i++) {
            Value dElem = fcn.domain[i];
            if (!(dElem instanceof IntValue)) {
              Assert.fail("Attempted to compare an integer with non-integer:\n" +
              Values.ppr(dElem.toString()) + ".");
            }
            if (((IntValue)dElem).val != (this.intv.low + i) ||
                !this.values[i].equals(fcn.values[i])) {
              return false;
            }
          }
        }
      }
      else {
        if (this.values.length != fcn.values.length) return false;
        if (fcn.intv != null) {
          for (int i = 0; i < this.domain.length; i++) {
            Value dElem = this.domain[i];
            if (!(dElem instanceof IntValue)) {
              Assert.fail("Attempted to compare an integer with non-integer:\n" +
              Values.ppr(dElem.toString()) + ".");
            }
            if (((IntValue)dElem).val != (fcn.intv.low + i) ||
                !this.values[i].equals(fcn.values[i])) {
              return false;
            }
          }
        }
        else {
          for (int i = 0; i < this.domain.length; i++) {
            if (!this.domain[i].equals(fcn.domain[i]) ||
                !this.values[i].equals(fcn.values[i])) {
              return false;
            }
          }
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
      Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
      "\nis an element of the function " + Values.ppr(this.toString()));
      return false;  // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() { return true; }

  @Override
  public final Value apply(Value arg, int control) {
    try {
    	Value result = this.select(arg);
      if (result == null) {
        Assert.fail("Attempted to apply function:\n" + Values.ppr(this.toString()) +
        "\nto argument " + Values.ppr(arg.toString()) + ", which is" +
        " not in the domain of the function.");
      }
      return result;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This one does not seem to be needed anymore.  */
  @Override
  public final Value apply(Value[] args, int control) {
    try {
      return this.apply(new TupleValue(args), EvalControl.Clear);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value select(Value arg) {
    try {

      if (this.intv != null) {
        // domain is represented as an integer interval:
        if (!(arg instanceof IntValue)) {
          Assert.fail("Attempted to apply function with integer domain to" +
                " the non-integer argument " + Values.ppr(arg.toString()));
        }
        int idx = ((IntValue)arg).val;
        if ((idx >= this.intv.low) && (idx <= this.intv.high)) {
          return this.values[idx - this.intv.low];
        }
      }
      else {
        // domain is represented as an array of values:
          int len = this.domain.length;
          for (int i = 0; i < len; i++) {
            if (this.domain[i].equals(arg)) {
              return this.values[i];
            }
          }
      }
      return null;

    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean assign(Value[] args, Value val) {
    try {

      if (this.intv != null) {
        // domain is represented as an integer interval:
        if (args.length != 1) {
          Assert.fail("Wrong number of function arguments.");
        }
        if (args[0] instanceof IntValue) {
          int idx = ((IntValue)args[0]).val;
          if ((idx >= this.intv.low) && (idx <= this.intv.high)) {
            int vIdx = idx - this.intv.low;
            if (this.values[vIdx] == UndefValue.ValUndef ||
                this.values[vIdx].equals(val)) {
              this.values[vIdx] = val;
              return true;
            }
            return false;
          }
        }
      }
      else {
        // domain is represented as an array of values:
        Value argv = new TupleValue(args);
        int len = this.domain.length;
        for (int i = 0; i < len; i++) {
          if (this.domain[i].equals(argv)) {
            if (this.values[i] == UndefValue.ValUndef ||
                this.values[i].equals(val)) {
              this.values[i] = val;
              return true;
            }
            return false;
          }
        }
      }
      Assert.fail("Function initialization out of domain.");
      return false;    // make compiler happy

    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept ex) {
    try {

      if (ex.idx >= ex.path.length) return ex.value;

      int flen = this.values.length;
      Value[] newValues = new Value[flen];
      for (int i = 0; i < flen; i++) {
        newValues[i] = this.values[i];
      }
      Value arg = ex.path[ex.idx];

      if (this.intv != null) {
        // domain is represented as an integer interval:
        if (arg instanceof IntValue) {
          int idx = ((IntValue)arg).val;
          if ((idx >= this.intv.low) && (idx <= this.intv.high)) {
            int vidx = idx - this.intv.low;
            ex.idx++;
            newValues[idx] = this.values[vidx].takeExcept(ex);
          }
          return new FcnRcdValue(this.intv, newValues);
        }
      }
      else {
        // domain is represented as an array of values:
        for (int i = 0; i < flen; i++) {
          if (arg.equals(this.domain[i])) {
            ex.idx++;
            newValues[i] = newValues[i].takeExcept(ex);
            Value[] newDomain = this.domain;
            if (!this.isNorm) {
              newDomain = new Value[flen];
              for (int j = 0; j < flen; j++) {
                newDomain[j] = this.domain[j];
              }
            }
            return new FcnRcdValue(newDomain, newValues, this.isNorm);
          }
        }
      }
      return this;

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
  public final Value getDomain() {
    try {
      if (this.intv != null) {
        return this.intv;
      }
      this.normalize();
      return new SetEnumValue(this.domain, true);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /**
   * Returns the domain of this FunctionRecordValue regardless of its internal
   * representation as either Value[] or IntervalValue as Value[].
   */
  public final Value[] getDomainAsValues() {
	  if (this.intv != null) {
		  return this.intv.asValues();
	  } else {
          return this.domain;		  
	  }
  }
  
  @Override
  public final int size() {
    try {
      this.normalize();
      return this.values.length;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }
  
  /**
   * {@link #size()} first normalizes, destructively, this instance; for inspections on the size without normalization
   * 	use this method.
   * 
   * @return
   */
  public int nonNormalizedSize() {
	  return values.length;
  }

  @Override
  public final Value toTuple() {
      if (this.intv != null) {
        if (this.intv.low != 1) return null;
        return new TupleValue(this.values);
      }
      int len = this.values.length;
      Value[] elems = new Value[len];
      for (int i = 0; i < len; i++) {
        if (!(this.domain[i] instanceof IntValue)) return null;
        int idx = ((IntValue)this.domain[i]).val;
        if (0 < idx && idx <= len) {
          if (elems[idx-1] != null) return null;
          elems[idx-1] = this.values[i];
        }
        else {
          return null;
        }
      }
      if (coverage) {cm.incSecondary(elems.length);}
      return new TupleValue(elems, cm);
  }

  @Override
  public final Value toRcd() {
      if (this.domain == null) return null;
      this.normalize();
      UniqueString[] vars = new UniqueString[this.domain.length];
      for (int i = 0; i < this.domain.length; i++) {
        if (!(this.domain[i] instanceof StringValue)) {
          return null;
        }
        vars[i] = ((StringValue)this.domain[i]).getVal();
      }
      if (coverage) {cm.incSecondary(this.values.length);}
      return new RecordValue(vars, this.values, this.isNormalized(), cm);
  }

  	@Override
	public final Value toFcnRcd() {
		return this;
	}
  
  /* Return true iff this function is in normal form. */
  @Override
  public final boolean isNormalized() { return this.isNorm; }

  /* This method normalizes (destructively) this function. */
  @Override
  public final Value normalize() {
    try {

      if (!this.isNorm) {
        // Assert.check(this.domain != null)
        int dlen = this.domain.length;
        for (int i = 1; i < dlen; i++) {
          int cmp = this.domain[0].compareTo(this.domain[i]);
          if (cmp == 0) {
            Assert.fail("The value\n" + this.domain[i] +
                  "\noccurs multiple times in the function domain.");
          }
          else if (cmp > 0) {
        	  Value tv = this.domain[0];
            this.domain[0] = this.domain[i];
            this.domain[i] = tv;
            tv = this.values[0];
            this.values[0] = this.values[i];
            this.values[i] = tv;
          }
        }
        for (int i = 2; i < dlen; i++) {
        	Value d = this.domain[i];
        	Value v = this.values[i];
          int j = i;
          int cmp;
          while ((cmp = d.compareTo(this.domain[j-1])) < 0) {
            this.domain[j] = this.domain[j-1];
            this.values[j] = this.values[j-1];
            j--;
          }
          if (cmp == 0) {
            Assert.fail("The value\n" + this.domain[i] +
                  "\noccurs multiple times in the function domain.");
          }
          this.domain[j] = d;
          this.values[j] = v;
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
      if (this.intv == null) {
        for (int i = 0; i < this.values.length; i++) {
          defined = defined && this.domain[i].isDefined();
        }
      }
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
      for (int i = 0; i < vals.length; i++) {
        vals[i] = (Value) this.values[i].deepCopy();
      }
      return new FcnRcdValue(this, vals);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean assignable(Value val) {
    try {
      boolean canAssign = ((val instanceof FcnRcdValue) &&
        this.values.length == ((FcnRcdValue)val).values.length);
      if (!canAssign) return false;
      FcnRcdValue fcn = (FcnRcdValue)val;
      for (int i = 0; i < this.values.length; i++) {
        canAssign = (canAssign &&
         this.domain[i].equals(fcn.domain[i]) &&
         this.values[i].assignable(fcn.values[i]));
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
			vos.writeByte(FCNRCDVALUE);
			int len = values.length;
			vos.writeNat(len);
			if (intv != null) {
				vos.writeByte((byte) 0);
				vos.writeInt(intv.low);
				vos.writeInt(intv.high);
				for (int i = 0; i < len; i++) {
					values[i].write(vos);
				}
			} else {
				vos.writeByte((isNormalized()) ? (byte) 1 : (byte) 2);
				for (int i = 0; i < len; i++) {
					domain[i].write(vos);
					values[i].write(vos);
				}
			}
		} else {
			vos.writeByte(DUMMYVALUE);
			vos.writeNat(index);
		}
	}

  /* The fingerprint method.  */
  @Override
  public final long fingerPrint(long fp) {
    try {
      this.normalize();
      int flen = this.values.length;
      fp = FP64.Extend(fp, FCNRCDVALUE);
      fp = FP64.Extend(fp, flen);
      if (this.intv == null) {
        for (int i = 0; i < flen; i++) {
          fp = this.domain[i].fingerPrint(fp);
          fp = this.values[i].fingerPrint(fp);
        }
      }
      else {
        for (int i = 0; i < flen; i++) {
          fp = FP64.Extend(fp, INTVALUE);
          fp = FP64.Extend(fp, i + this.intv.low);
          fp = this.values[i].fingerPrint(fp);
        }
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
      int flen = this.domain.length;
      Value[] vals = new Value[flen];

      boolean vchanged = false;
      for (int i = 0; i < flen; i++) {
        vals[i] = (Value) this.values[i].permute(perm);
        vchanged = vchanged || (vals[i] != this.values[i]);
      }

      if (this.intv == null) {
    	  Value[] dom = new Value[flen];
        boolean dchanged = false;
        for (int i = 0; i < flen; i++) {
          dom[i] = (Value) this.domain[i].permute(perm);
          dchanged = dchanged || (dom[i] != this.domain[i]);
        }

        if (dchanged) {
          return new FcnRcdValue(dom, vals, false);
        }
        else if (vchanged) {
          return new FcnRcdValue(this.domain, vals, true);
        }
      }
      else {
        if (vchanged) {
          return new FcnRcdValue(this.intv, vals);
        }
      }
      return this;

    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private static final boolean isName(String name) {
    int len = name.length();
    boolean hasLetter = false;

    for (int idx = 0; idx < len; idx++) {
      char ch = name.charAt(idx);
      if (ch == '_') continue;
      if (!Character.isLetterOrDigit(ch)) return false;
      hasLetter = hasLetter || Character.isLetter(ch);
    }

    return hasLetter && (len < 4 || (!name.startsWith("WF_") && !name.startsWith("SF_")));
  }

  private final boolean isRcd() {
    if (this.intv != null) return false;
    for (int i = 0; i < this.domain.length; i++) {
      Value dval = this.domain[i];
      boolean isName = ((dval instanceof StringValue) &&
      isName(((StringValue)dval).val.toString()));
      if (!isName) return false;
    }
    return true;
  }

  private final boolean isTuple() {
    if (this.intv != null) {
      return (this.intv.low == 1);
    }
    for (int i = 0; i < this.domain.length; i++) {
      if (!(this.domain[i] instanceof IntValue)) {
        return false;
      }
    }
    this.normalize();
    for (int i = 0; i < this.domain.length; i++) {
      if (((IntValue)this.domain[i]).val != (i+1)) {
        return false;
      }
    }
    return true;
  }

  /* The string representation of the value.  */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {

      int len = this.values.length;
      if (len == 0) {
        sb.append("<< >>");
      }
      else if (this.isRcd()) {
        sb.append("[");
        sb.append(((StringValue)this.domain[0]).val + TLAConstants.RECORD_ARROW);
        sb = this.values[0].toString(sb, offset, swallow);

        for (int i = 1; i < len; i++) {
          sb.append(", ");
          sb.append(((StringValue)this.domain[i]).val + TLAConstants.RECORD_ARROW);
          sb = this.values[i].toString(sb, offset, swallow);
        }
        sb.append("]");
      }
      else if (this.isTuple()) {
        // It is actually a sequence:
        sb = sb.append("<<");
        sb = this.values[0].toString(sb, offset, swallow);

        for (int i = 1; i < len; i++) {
          sb.append(", ");
          sb = this.values[i].toString(sb, offset, swallow);
        }
        sb.append(">>");
      }
      else {
        sb = sb.append("(");
        sb = this.domain[0].toString(sb, offset, swallow);
        sb.append(" :> ");
        sb = this.values[0].toString(sb, offset, swallow);

        for (int i = 1; i < len; i++) {
          sb.append(" @@ ");
          sb = this.domain[i].toString(sb, offset, swallow);
          sb.append(" :> ");
          sb = this.values[i].toString(sb, offset, swallow);
        }
        sb.append(")");
      }
      return sb;

    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	public static IValue createFrom(final IValueInputStream vos) throws IOException {
		final int index = vos.getIndex();
		final int len = vos.readNat();
		final int info = vos.readByte();
		Value res;
		final Value[] rvals = new Value[len];
		if (info == 0) {
			final int low = vos.readInt();
			final int high = vos.readInt();
			for (int i = 0; i < len; i++) {
				rvals[i] = (Value) vos.read();
			}
			final IntervalValue intv = new IntervalValue(low, high);
			res = new FcnRcdValue(intv, rvals);
		} else {
			final Value[] dvals = new Value[len];
			for (int i = 0; i < len; i++) {
				dvals[i] = (Value) vos.read();
				rvals[i] = (Value) vos.read();
			}
			res = new FcnRcdValue(dvals, rvals, (info == 1));
		}
		vos.assign(res, index);
		return res;
	}

	public static IValue createFrom(final ValueInputStream vos, final Map<String, UniqueString> tbl) throws IOException {
		final int index = vos.getIndex();
		final int len = vos.readNat();
		final int info = vos.readByte();
		Value res;
		final Value[] rvals = new Value[len];
		if (info == 0) {
			final int low = vos.readInt();
			final int high = vos.readInt();
			for (int i = 0; i < len; i++) {
				rvals[i] = (Value) vos.read(tbl);
			}
			final IntervalValue intv = new IntervalValue(low, high);
			res = new FcnRcdValue(intv, rvals);
		} else {
			final Value[] dvals = new Value[len];
			for (int i = 0; i < len; i++) {
				dvals[i] = (Value) vos.read(tbl);
				rvals[i] = (Value) vos.read(tbl);
			}
			res = new FcnRcdValue(dvals, rvals, (info == 1));
		}
		vos.assign(res, index);
		return res;
	}
}
