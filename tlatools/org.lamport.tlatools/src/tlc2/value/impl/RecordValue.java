// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:15:47 PST by lamport
//      modified on Fri Aug 10 15:09:07 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.EOFException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.FingerprintException;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.ValueInputStream;
import tlc2.value.Values;
import util.Assert;
import util.TLAConstants;
import util.UniqueString;

public class RecordValue extends Value implements Applicable {
  private static final UniqueString BLI = UniqueString.of("beginLine");
  private static final UniqueString BCOL = UniqueString.of("beginColumn");
  private static final UniqueString ELI = UniqueString.of("endLine");
  private static final UniqueString ECOL = UniqueString.of("endColumn");
  private static final UniqueString MOD = UniqueString.of("module");
  private static final UniqueString NAME = UniqueString.of("name");
  private static final UniqueString LOC = UniqueString.of("location");
  private static final UniqueString CTXT = UniqueString.of("context");
  private static final UniqueString ACTION = UniqueString.of("_action");

  public final UniqueString[] names;   // the field names
  public final Value[] values;         // the field values
  private boolean isNorm;
  public static final RecordValue EmptyRcd = new RecordValue(new UniqueString[0], new Value[0], true);

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
  
  public RecordValue(UniqueString name, Value v, boolean isNorm) {
	  this(new UniqueString[] {name}, new Value[] {v}, isNorm);
  }
  
  public RecordValue(UniqueString name, Value v) {
	  this(new UniqueString[] {name}, new Value[] {v}, false);
  }

	// See
	// https://github.com/tlaplus/CommunityModules/commit/12cc3c6046d49ceaf2d0de8ce7558d8e2f4e53ad#diff-9a781a1a0e9b833becf01e1979ac6c5a9d49561c6b41cfbd70cfd75df1716867R86
	// where this would have been useful. Consider refactoring the CM module
	// override once sufficient time has passed that we can expect most users to be
	// on a version of TLC with this constructor.
	public RecordValue(final Map<UniqueString, ? extends Value> m) {
		final List<Map.Entry<UniqueString, ? extends Value>> entries = new ArrayList<>(m.entrySet());

		this.names = new UniqueString[entries.size()];
		this.values = new Value[entries.size()];

		for (int i = 0; i < entries.size(); i++) {
			this.names[i] = entries.get(i).getKey();
			this.values[i] = entries.get(i).getValue();
		}
	}

  public RecordValue(final Location location) {
		this.names = new UniqueString[5];
		this.values = new Value[this.names.length];

		this.names[0] = BLI;
		this.values[0] = IntValue.gen(location.beginLine());

		this.names[1] = BCOL;
		this.values[1] = IntValue.gen(location.beginColumn());

		this.names[2] = ELI;
		this.values[2] = IntValue.gen(location.endLine());

		this.names[3] = ECOL;
		this.values[3] = IntValue.gen(location.endColumn());
		
		this.names[4] = MOD;
		this.values[4] = new StringValue(location.sourceAsUniqueString());
		
		this.isNorm = false;
  }

  public RecordValue(final Action action) {
		this.names = new UniqueString[2];
		this.values = new Value[this.names.length];

		this.names[0] = NAME;
		this.values[0] = new StringValue(action.getName());
		
		this.names[1] = LOC;
		this.values[1] = new RecordValue(action.getDefinition());
		
		this.isNorm = false;
  }

  public RecordValue(final Action action, final Context ctxt) {
		this.names = new UniqueString[3];
		this.values = new Value[this.names.length];

		this.names[0] = NAME;
		this.values[0] = new StringValue(action.getName());
		
		this.names[1] = LOC;
		this.values[1] = new RecordValue(action.getDefinition());
		
		this.names[2] = CTXT;
		this.values[2] = new RecordValue(ctxt.toMap());
		
		this.isNorm = false;
  }

  public RecordValue(final TLCStateInfo info) {
	  this(info.state);
  }

  public RecordValue(final TLCState state) {
		final OpDeclNode[] vars = state.getVars();
		
		this.names = new UniqueString[vars.length];
		this.values = new Value[vars.length];

		for (int i = 0; i < vars.length; i++) {
			this.names[i] = vars[i].getName();
			this.values[i] = (Value) state.lookup(this.names[i]); 
		}

		this.isNorm = false;
  }

  public RecordValue(final TLCState state, final Action action) {
		final OpDeclNode[] vars = state.getVars();
		
		this.names = new UniqueString[vars.length + 1];
		this.values = new Value[vars.length + 1];

		//TODO: _action too verbose?
		this.names[0] = ACTION;
		this.values[0] = new RecordValue(action, action.con);
		
		for (int i = 0; i < vars.length; i++) {
			this.names[i+1] = vars[i].getName();
			this.values[i+1] = (Value) state.lookup(this.names[i+1]); 
		}
		
		this.isNorm = false;
  }

  public RecordValue(final TLCState state, final Value defVal) {
	  this(state);
		// if state.lookup in this returned null, replace null with defVal.
		for (int i = 0; i < this.values.length; i++) {
			if (this.values[i] == null) {
				this.values[i] = defVal;
			}
		}
  }

  	/**
	 * Create RecordValue out of pair of states (s, t) such that the variable names
	 * of s become record keys as is and the variables of t become record keys with
	 * a ' appended.
	 */
  public RecordValue(final TLCState state, final TLCState successor, final Value defVal) {
	  assert state.getVars().length == successor.getVars().length;
	  
		final OpDeclNode[] vars = state.getVars();
		
		this.names = new UniqueString[vars.length * 2];
		this.values = new Value[vars.length * 2];

		for (int i = 0; i < vars.length; i++) {
			final int j = i * 2;
			final UniqueString var = vars[i].getName();

			this.names[j] = UniqueString.of(var + " ");
			this.names[j+1] = UniqueString.of(var + "'");

			this.values[j] = (Value) state.lookup(var);
			if (this.values[j] == null) {
				this.values[j] = defVal;
			}
			
			this.values[j+1] = (Value) successor.lookup(var);
			if (this.values[j+1] == null) {
				this.values[j+1] = defVal;
			}
		}

		this.isNorm = false;
  }

  @Override
  public final byte getKind() { return RECORDVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      RecordValue rcd = obj instanceof Value ? (RecordValue) ((Value)obj).toRcd() : null;
      if (rcd == null) {
        if (obj instanceof ModelValue) {
            return ((ModelValue) obj).modelValueCompareTo(this);
        }
        Assert.fail("Attempted to compare record:\n" + Values.ppr(this.toString()) +
        "\nwith non-record\n" + Values.ppr(obj.toString()), getSource());
      }
      this.normalize();
      rcd.normalize();
      int len = this.names.length;
      int cmp = len - rcd.names.length;
      if (cmp == 0) {
    	// First, compare the (equicardinal) domains.
        for (int i = 0; i < len; i++) {
          cmp = this.names[i].compareTo(rcd.names[i]);
          if (cmp != 0) return cmp;
        }
        // Then, compare values iff domains are equal.
        for (int i = 0; i < len; i++) {
          cmp = this.values[i].compareTo(rcd.values[i]);
          if (cmp != 0) return cmp;
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
        "\nwith non-record\n" + Values.ppr(obj.toString()), getSource());
      }
      this.normalize();
      rcd.normalize();
      int len = this.names.length;
      if (len != rcd.names.length) return false;
  	  // First, compare the (equicardinal) domains.
      for (int i = 0; i < len; i++) {
        if (!(this.names[i].equals(rcd.names[i]))) {
        	return false;
        }
      }
      // Then, compare values iff domains are equal.
      for (int i = 0; i < len; i++) {
        if (!(this.values[i].equals(rcd.values[i]))) {
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
      Assert.fail("Attempted to check if element:\n" + Values.ppr(elem.toString()) +
                  "\nis in the record:\n" + Values.ppr(this.toString()), getSource());
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
        Assert.fail("Attempted to access record by a non-string argument: " + Values.ppr(arg.toString()), getSource());
      }
      UniqueString name = ((StringValue)arg).getVal();
      int rlen = this.names.length;
      for (int i = 0; i < rlen; i++) {
        if (name.equals(this.names[i])) {
          return this.values[i];
        }
      }
      Assert.fail("Attempted to access nonexistent field '" + name +
          "' of record\n" + Values.ppr(this.toString()), getSource());
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
        Assert.fail("Attempted to apply record to more than one arguments.", getSource());
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
        Assert.fail("Attempted to access record by a non-string argument: " + Values.ppr(arg.toString()), getSource());
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

//  public final boolean assign(UniqueString name, Value val) {
//    try {
//      for (int i = 0; i < this.names.length; i++) {
//        if (name.equals(this.names[i])) {
//          if (this.values[i] == UndefValue.ValUndef ||
//              this.values[i].equals(val)) {
//            this.values[i] = val;
//            return true;
//          }
//          return false;
//        }
//      }
//      Assert.fail("Attempted to assign to nonexistent record field " + name + ".", getSource());
//      return false;    // make compiler happy
//    }
//    catch (RuntimeException | OutOfMemoryError e) {
//      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
//      else { throw e; }
//    }
//  }

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
            Assert.fail("Field name " + this.names[i] + " occurs multiple times in record.", getSource());
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
            Assert.fail("Field name " + this.names[i] + " occurs multiple times in record.", getSource());
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
        sb.append(this.names[0] + TLAConstants.RECORD_ARROW);
        sb = this.values[0].toString(sb, offset, swallow);
      }
      for (int i = 1; i < len; i++) {
        sb.append(", ");
        sb.append(this.names[i] + TLAConstants.RECORD_ARROW);
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

	public static IValue createFrom(final ValueInputStream vos, final Map<String, UniqueString> tbl) throws EOFException, IOException {
		final int index = vos.getIndex();
		int len = vos.readInt();
		if (len < 0) {
			len = -len;
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
				names[i] = UniqueString.read(vos.getInputStream(), tbl);
				vos.assign(names[i], index1);
			}
			vals[i] = (Value) vos.read(tbl);
		}
		// If a RecordValue is de-serialized with a potentially different UniqueString
		// table, the RecordValue is not guaranteed to be normalized.
		final Value res = new RecordValue(names, vals, false);
		vos.assign(res, index);
		return res;
	}

	public TLCState toState() {
			final TLCState state = TLCState.Empty.createEmpty();
			final OpDeclNode[] vars = state.getVars();
			for (int i = 0; i < vars.length; i++) {
				final UniqueString name = vars[i].getName();
				int rlen = this.names.length;
				for (int j = 0; j < rlen; j++) {
					if (name.equals(this.names[j])) {
						state.bind(name, this.values[j]);
					}
				}
			}
			return new PrintTLCState(this, state);
		}

		private static final class PrintTLCState extends TLCState {

			private final RecordValue rcd;
			private final TLCState state;

			public PrintTLCState(RecordValue recordValue, final TLCState state) {
				this.rcd = recordValue;
				this.state = state;
			}

			@Override
			public String toString() {
				final StringBuffer result = new StringBuffer();
				int vlen = rcd.names.length;
				if (vlen == 1) {
					result.append(rcd.names[0].toString());
					result.append(" = ");
					result.append(Values.ppr(rcd.values[0]));
					result.append("\n");
				} else {
					for (int i = 0; i < vlen; i++) {
						UniqueString key = rcd.names[i];
						result.append("/\\ ");
						result.append(key.toString());
						result.append(" = ");
						result.append(Values.ppr(rcd.values[i]));
						result.append("\n");
					}
				}
				return result.toString();
			}

			@Override
			public int hashCode() {
				return this.state.hashCode();
			}

			@Override
			public boolean equals(Object obj) {
				return this.state.equals(obj);
			}

			@Override
			public long fingerPrint() {
				return this.state.fingerPrint();
			}

			@Override
			public boolean allAssigned() {
				return this.state.allAssigned();
			}

			@Override
			public String toString(TLCState lastState) {
				return this.state.toString(lastState);
			}

			@Override
			public TLCState bind(UniqueString name, IValue value) {
				return this.state.bind(name, value);
			}

			@Override
			public TLCState bind(SymbolNode id, IValue value) {
				return this.state.bind(id, value);
			}

			@Override
			public TLCState unbind(UniqueString name) {
				return this.state.unbind(name);
			}

			@Override
			public IValue lookup(UniqueString var) {
				return this.state.lookup(var);
			}

			@Override
			public boolean containsKey(UniqueString var) {
				return this.state.containsKey(var);
			}

			@Override
			public TLCState copy() {
				return this.state.copy();
			}

			@Override
			public TLCState deepCopy() {
				return this.state.deepCopy();
			}

			@Override
			public StateVec addToVec(StateVec states) {
				return this.state.addToVec(states);
			}

			@Override
			public void deepNormalize() {
				this.state.deepNormalize();
			}

			@Override
			public Set<OpDeclNode> getUnassigned() {
				return this.state.getUnassigned();
			}

			@Override
			public TLCState createEmpty() {
				return this.state.createEmpty();
			}
		}

		@Override
		public List<TLCVariable> getTLCVariables(final TLCVariable prototype, Random rnd) {
			final List<TLCVariable> nestedVars = new ArrayList<>(values.length);
			for (int i = 0; i < names.length; i++) {
				final UniqueString uniqueString = names[i];
				final Value v = values[i];
				final TLCVariable nested = prototype.newInstance(uniqueString.toString(), v, rnd);
				nested.setValue(v.toString());
				nested.setType(v.getTypeString());
				nestedVars.add(nested);
			}
			return nestedVars;
		}
}
