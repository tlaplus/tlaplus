// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.value;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

import tlc2.TLCGlobals;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import util.BufferedDataInputStream;
import util.FileUtil;
import util.IDataInputStream;
import util.UniqueString;
import util.WrongInvocationException;

public final class ValueInputStream implements ValueConstants, IValueInputStream {

  private final BufferedDataInputStream dis;
  private final HandleTable handles;
  
  public ValueInputStream(InputStream in) throws IOException 
  {
      // SZ Feb 24, 2009: FileUtil refactoring
    this.dis = new BufferedDataInputStream(in);
    this.handles = new HandleTable();
  }

  public ValueInputStream(File file, final boolean compressed) throws IOException 
  {
	  this(FileUtil.newBdFIS(compressed, file));
  }
  
  public ValueInputStream(File file) throws IOException 
  {
	  this(file, TLCGlobals.useGZIP);
  }

  public ValueInputStream(String fname) throws IOException {
      this(new File(fname));
  }

	@Override
	public final IValue read() throws IOException {
		final byte kind = this.dis.readByte();

		switch (kind) {
		case BOOLVALUE: {
			return (this.dis.readBoolean()) ? BoolValue.ValTrue : BoolValue.ValFalse;
		}
		case INTVALUE: {
			return IntValue.gen(this.dis.readInt());
		}
		case STRINGVALUE: {
			return StringValue.createFrom(this);
		}
		case MODELVALUE: {
			return ModelValue.mvs[this.dis.readShort()];
		}
		case INTERVALVALUE: {
			return new IntervalValue(this.dis.readInt(), this.dis.readInt());
		}
		case RECORDVALUE: {
			return RecordValue.createFrom(this);
		}
		case FCNRCDVALUE: {
			return FcnRcdValue.createFrom(this);
		}
		case SETENUMVALUE: {
			return SetEnumValue.createFrom(this);
		}
		case TUPLEVALUE: {
			return TupleValue.createFrom(this);
		}
		case DUMMYVALUE: {
			return (IValue) this.handles.getValue(this.readNat());
		}
		default: {
			throw new WrongInvocationException("ValueInputStream: Can not unpickle a value of kind " + kind);
		}
		}
	}
	
	/**
	 * This used to be readExternal, but the tbl parameter did not end up being useful.
	 * It was meant to allow using a different string intern table, but as a result
	 * required all deserialized string values to be known ahead of time (in the map).
	 * 
	 * This stub calls readExternal, ignoring tbl and directly loading new strings into
	 * this TLC's global intern table instead. It is left here to avoid Java method
	 * errors with community modules, which call this signature in particular.
	 * 
	 * TODO:
	 * - Once all practically deployed TLCs that don't have readExternal are phased out,
	 *   change community modules to call readExternal.
	 * - Once all practically deployed community modules that use this method are phased out,
	 *   delete it.
	 */
	@Deprecated
	public final IValue read(final Map<String, UniqueString> tbl) throws IOException {
		return readExternal();
	}
	
	/**
	 * Safely read a value from an external source that may have a different intern table for UniqueStrings.
	 * By contrast, {@link #read()} assumes that the value was written by this process using the same intern table.
	 */
	public final IValue readExternal() throws IOException {
		final byte kind = this.dis.readByte();

		switch (kind) {
		case BOOLVALUE: {
			return (this.dis.readBoolean()) ? BoolValue.ValTrue : BoolValue.ValFalse;
		}
		case INTVALUE: {
			return IntValue.gen(this.dis.readInt());
		}
		case STRINGVALUE: {
			return StringValue.createFromExternal(this);
		}
		case MODELVALUE: {
			return ModelValue.mvs[this.dis.readShort()];
		}
		case INTERVALVALUE: {
			return new IntervalValue(this.dis.readInt(), this.dis.readInt());
		}
		case RECORDVALUE: {
			return RecordValue.createFromExternal(this);
		}
		case FCNRCDVALUE: {
			return FcnRcdValue.createFromExternal(this);
		}
		case SETENUMVALUE: {
			return SetEnumValue.createFromExternal(this);
		}
		case TUPLEVALUE: {
			return TupleValue.createFromExternal(this);
		}
		case DUMMYVALUE: {
			return (IValue) this.handles.getValue(this.readNat());
		}
		default: {
			throw new WrongInvocationException("ValueInputStream: Can not unpickle a value of kind " + kind);
		}
		}
	}
 
  @Override
  public final int readShort() throws IOException {
	    return this.dis.readShort();
  }

  @Override
  public final int readInt() throws IOException {
    return this.dis.readInt();
  }

  @Override
  public final long readLong() throws IOException {
    return this.dis.readLong();
  }
  
  @Override
  public final void close() throws IOException {
    this.dis.close();
  }

  @Override
  public final int readNat() throws IOException {
    int res = this.dis.readShort();
    if (res >= 0) return res;
    res = (res << 16) | (this.dis.readShort() & 0xFFFF);
    return -res;
  }
  
  @Override
  public final short readShortNat() throws IOException {
	short res = this.dis.readByte();
	if (res >= 0) return res;
	return (short) -((res << 8) | (this.dis.readByte() & 0xFF));
  }
  
  @Override
  public final long readLongNat() throws IOException {
    long res = this.dis.readInt();
    if (res >= 0) return res;
    res = (res << 32) | ((long)this.dis.readInt() & 0xFFFFFFFFL);
    return -res;
  }

	@Override
	public final byte readByte() throws EOFException, IOException {
		return this.dis.readByte();
	}

	@Override
	public final void assign(final Object obj, final int idx) {
		this.handles.assign(obj, idx);
	}

	@Override
	public final int getIndex() {
		return handles.getIndex();
	}

	@Override
	public final IDataInputStream getInputStream() {
		return dis;
	}

	@Override
	public final UniqueString getValue(int idx) {
		return (UniqueString) this.handles.getValue(idx);
	}
	
	@Override
	public final boolean atEOF() {
		return dis.atEOF();
	}

  // @see ValueOutputStream#put
  private static class HandleTable {
    private Object[] values;
    private int index;
    
    HandleTable() {
      this.values = new Object[16];
      this.index = 0;
    }

    final int getIndex() {
      if (this.index >= this.values.length) {
	Object[] newValues = new Object[this.index*2];
	System.arraycopy(this.values, 0, newValues, 0, this.index);
	this.values = newValues;
      }
      return this.index++;
    }

    final void assign(Object val, int idx) {
      this.values[idx] = val;
    }

    final Object getValue(int idx) { return this.values[idx]; }

  }
}
