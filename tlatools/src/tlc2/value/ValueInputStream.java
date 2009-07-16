// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.value;

import java.io.File;
import java.io.IOException;

import tlc2.TLCGlobals;
import util.BufferedDataInputStream;
import util.FileUtil;
import util.UniqueString;
import util.WrongInvocationException;

public final class ValueInputStream implements ValueConstants {

  private BufferedDataInputStream dis;
  private HandleTable handles;

  public ValueInputStream(File file) throws IOException 
  {
      // SZ Feb 24, 2009: FileUtil refactoring
    this.dis = FileUtil.newBdFIS(TLCGlobals.useGZIP, file);
    this.handles = new HandleTable();
  }

  public ValueInputStream(String fname) throws IOException {
      this(new File(fname));
  }

  public final Value read() throws IOException {
    byte kind = this.dis.readByte();

    switch (kind) {
    case BOOLVALUE:
      {
	boolean b = this.dis.readBoolean();
	return (b) ? ValTrue : ValFalse;
      }
    case INTVALUE:
      {
	int x = this.dis.readInt();
	return IntValue.gen(x);
      }
    case STRINGVALUE:
      {
	UniqueString str = UniqueString.read(this.dis);
	Value res = new StringValue(str);
	int index = this.handles.getIndex();
	this.handles.assign(res, index);
	return res;
      }
    case MODELVALUE:
      {
	int index = this.dis.readShort();
	return ModelValue.mvs[index];
      }
    case INTERVALVALUE:
      {
	int low = this.dis.readInt();
	int hi = this.dis.readInt();
	return new IntervalValue(low, hi);
      }
    case RECORDVALUE:
      {
	int index = this.handles.getIndex();
	boolean isNorm = true;
	int len = this.dis.readInt();
	if (len < 0) { len = -len; isNorm = false; }
	UniqueString[] names = new UniqueString[len];
	Value[] vals = new Value[len];
	for (int i = 0; i < len; i++) {
	  byte kind1 = this.dis.readByte();
	  if (kind1 == DUMMYVALUE) {
	    int index1 = this.readNat();
	    names[i] = (UniqueString)this.handles.getValue(index1);
	  }
	  else {
	    int index1 = this.handles.getIndex();
	    names[i] = UniqueString.read(this.dis);
	    this.handles.assign(names[i], index1);
	  }
	  vals[i] = this.read();
	}
	Value res = new RecordValue(names, vals, isNorm);
	this.handles.assign(res, index);
	return res;
      }
    case FCNRCDVALUE:
      {
	int index = this.handles.getIndex();
	int len = this.readNat();
	int info = this.dis.readByte();
	Value res;
	Value[] rvals = new Value[len];
	if (info == 0) {
	  int low = this.dis.readInt();
	  int high = this.dis.readInt();
	  for (int i = 0; i < len; i++) {
	    rvals[i] = this.read();
	  }
	  IntervalValue intv = new IntervalValue(low, high);
	  res = new FcnRcdValue(intv, rvals);
	}
	else {
	  Value[] dvals = new Value[len];
	  for (int i = 0; i < len; i++) {
	    dvals[i] = this.read();
	    rvals[i] = this.read();
	  }
	  res = new FcnRcdValue(dvals, rvals, (info == 1));
	}
	this.handles.assign(res, index);
	return res;
      }
    case SETENUMVALUE:
      {
	int index = this.handles.getIndex();
	boolean isNorm = true;
	int len = this.dis.readInt();
	if (len < 0) { len = -len; isNorm = false; }
	Value[] elems = new Value[len];
	for (int i = 0; i < len; i++) {
	  elems[i] = this.read();
	}
	Value res = new SetEnumValue(elems, isNorm);
	this.handles.assign(res, index);
	return res;
      }
    case TUPLEVALUE:
      {
	int index = this.handles.getIndex();
	int len = this.readNat();
	Value[] elems = new Value[len];
	for (int i = 0; i < len; i++) {
	  elems[i] = this.read();
	}
	Value res = new TupleValue(elems);
	this.handles.assign(res, index);
	return res;
      }
    case DUMMYVALUE:
      {
	int index = this.readNat();
	return (Value)this.handles.getValue(index);
      }
    default:
      {
	throw new WrongInvocationException("ValueInputStream: Can not unpickle a value of kind " + kind);
      }
    }      
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
  
  public final long readLongNat() throws IOException {
    long res = this.dis.readInt();
    if (res >= 0) return res;
    res = (res << 32) | ((long)this.dis.readInt() & 0xFFFFFFFFL);
    return -res;
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
