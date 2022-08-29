// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.value;

import tlc2.TLCGlobals;
import tlc2.value.impl.*;
import util.*;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

public final class ValueInputStream implements ValueConstants, IValueInputStream {

    private final BufferedDataInputStream dis;
    private final HandleTable handles;

    public ValueInputStream(final InputStream in) throws IOException {
        // SZ Feb 24, 2009: FileUtil refactoring
        this.dis = new BufferedDataInputStream(in);
        this.handles = new HandleTable();
    }

    public ValueInputStream(final File file, final boolean compressed) throws IOException {
        this(FileUtil.newBdFIS(compressed, file));
    }

    public ValueInputStream(final File file) throws IOException {
        this(file, TLCGlobals.useGZIP);
    }

    public ValueInputStream(final String fname) throws IOException {
        this(new File(fname));
    }

    @Override
    public IValue read() throws IOException {
        final byte kind = this.dis.readByte();

        switch (kind) {
            case BOOLVALUE -> {
                return (this.dis.readBoolean()) ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            case INTVALUE -> {
                return IntValue.gen(this.dis.readInt());
            }
            case STRINGVALUE -> {
                return StringValue.createFrom(this);
            }
            case MODELVALUE -> {
                return ModelValue.mvs[this.dis.readShort()];
            }
            case INTERVALVALUE -> {
                return new IntervalValue(this.dis.readInt(), this.dis.readInt());
            }
            case RECORDVALUE -> {
                return RecordValue.createFrom(this);
            }
            case FCNRCDVALUE -> {
                return FcnRcdValue.createFrom(this);
            }
            case SETENUMVALUE -> {
                return SetEnumValue.createFrom(this);
            }
            case TUPLEVALUE -> {
                return TupleValue.createFrom(this);
            }
            case DUMMYVALUE -> {
                return (IValue) this.handles.getValue(this.readNat());
            }
            default -> throw new WrongInvocationException("ValueInputStream: Can not unpickle a value of kind " + kind);
        }
    }

    public IValue read(final Map<String, UniqueString> tbl) throws IOException {
        final byte kind = this.dis.readByte();

        switch (kind) {
            case BOOLVALUE -> {
                return (this.dis.readBoolean()) ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            case INTVALUE -> {
                return IntValue.gen(this.dis.readInt());
            }
            case STRINGVALUE -> {
                return StringValue.createFrom(this, tbl);
            }
            case MODELVALUE -> {
                return ModelValue.mvs[this.dis.readShort()];
            }
            case INTERVALVALUE -> {
                return new IntervalValue(this.dis.readInt(), this.dis.readInt());
            }
            case RECORDVALUE -> {
                return RecordValue.createFrom(this, tbl);
            }
            case FCNRCDVALUE -> {
                return FcnRcdValue.createFrom(this, tbl);
            }
            case SETENUMVALUE -> {
                return SetEnumValue.createFrom(this, tbl);
            }
            case TUPLEVALUE -> {
                return TupleValue.createFrom(this, tbl);
            }
            case DUMMYVALUE -> {
                return (IValue) this.handles.getValue(this.readNat());
            }
            default -> throw new WrongInvocationException("ValueInputStream: Can not unpickle a value of kind " + kind);
        }
    }

    @Override
    public int readShort() throws IOException {
        return this.dis.readShort();
    }

    @Override
    public int readInt() throws IOException {
        return this.dis.readInt();
    }

    @Override
    public long readLong() throws IOException {
        return this.dis.readLong();
    }

    @Override
    public void close() throws IOException {
        this.dis.close();
    }

    @Override
    public int readNat() throws IOException {
        int res = this.dis.readShort();
        if (res >= 0) return res;
        res = (res << 16) | (this.dis.readShort() & 0xFFFF);
        return -res;
    }

    @Override
    public short readShortNat() throws IOException {
        final short res = this.dis.readByte();
        if (res >= 0) return res;
        return (short) -((res << 8) | (this.dis.readByte() & 0xFF));
    }

    @Override
    public long readLongNat() throws IOException {
        long res = this.dis.readInt();
        if (res >= 0) return res;
        res = (res << 32) | ((long) this.dis.readInt() & 0xFFFFFFFFL);
        return -res;
    }

    @Override
    public byte readByte() throws IOException {
        return this.dis.readByte();
    }

    @Override
    public void assign(final Object obj, final int idx) {
        this.handles.assign(obj, idx);
    }

    @Override
    public int getIndex() {
        return handles.getIndex();
    }

    @Override
    public IDataInputStream getInputStream() {
        return dis;
    }

    @Override
    public UniqueString getValue(final int idx) {
        return (UniqueString) this.handles.getValue(idx);
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
                final Object[] newValues = new Object[this.index * 2];
                System.arraycopy(this.values, 0, newValues, 0, this.index);
                this.values = newValues;
            }
            return this.index++;
        }

        final void assign(final Object val, final int idx) {
            this.values[idx] = val;
        }

        final Object getValue(final int idx) {
            return this.values[idx];
        }

    }
}
