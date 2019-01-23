// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.value;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;

import tlc2.TLCGlobals;
import util.BufferedDataInputStream;
import util.FileUtil;
import util.UniqueString;
import util.WrongInvocationException;

public final class ValueInputStream implements ValueConstants {

  private final BufferedDataInputStream dis;
  private final HandleTable handles;

  public ValueInputStream(File file) throws IOException 
  {
      // SZ Feb 24, 2009: FileUtil refactoring
    this.dis = FileUtil.newBdFIS(TLCGlobals.useGZIP, file);
    this.handles = new HandleTable();
  }

  public ValueInputStream(String fname) throws IOException {
      this(new File(fname));
  }

	public final IValue read() throws IOException {
		final byte kind = this.dis.readByte();

		switch (kind) {
		case BOOLVALUE: {
			return (this.dis.readBoolean()) ? ValTrue : ValFalse;
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
  
  public final int readShort() throws IOException {
	    return this.dis.readShort();
  }

  public final int readInt() throws IOException {
    return this.dis.readInt();
  }

  public final long readLong() throws IOException {
    return this.dis.readLong();
  }
  
  public final void close() throws IOException {
    this.dis.close();
  }

  public final int readNat() throws IOException {
    int res = this.dis.readShort();
    if (res >= 0) return res;
    res = (res << 16) | (this.dis.readShort() & 0xFFFF);
    return -res;
  }
  
  public final short readShortNat() throws IOException {
	short res = this.dis.readByte();
	if (res >= 0) return res;
	return (short) -((res << 8) | (this.dis.readByte() & 0xFF));
  }
  
  public final long readLongNat() throws IOException {
    long res = this.dis.readInt();
    if (res >= 0) return res;
    res = (res << 32) | ((long)this.dis.readInt() & 0xFFFFFFFFL);
    return -res;
  }

	public byte readByte() throws EOFException, IOException {
		return this.dis.readByte();
	}

	public final void assign(final Object obj, final int idx) {
		this.handles.assign(obj, idx);
	}

	public final int getIndex() {
		return handles.getIndex();
	}

	public final BufferedDataInputStream getInputStream() {
		return dis;
	}

	public final UniqueString getValue(int idx) {
		return (UniqueString) this.handles.getValue(idx);
	}

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
