// Copyright (c) 2024, Oracle and/or its affiliates.

package tlc2.util;

import java.util.BitSet;

/**
 * An "abstract" in-memory version of {@link RandomAccessFile} that only tracks which bytes are well-defined, not the
 * actual value of those bytes.
 *
 * @see BufferedRandomAccessFileFuzzTest
 */
public class AbstractFileState {

    private int cursor = 0;
    private int length = 0;
    private final BitSet writtenPositions = new BitSet(1024); // initial size is just a hint

    public void writeBytes(int count) {
        int newPos = cursor + count;
        writtenPositions.set(cursor, newPos);
        cursor = newPos;
        length = Math.max(length, cursor);
    }

    public void readBytes(int count) {
        cursor = Math.max(Math.min(cursor + count, length), cursor);
    }

    public boolean readWouldBeWellDefined(int count) {
        int end = Math.min(cursor + count, length);
        return writtenPositions.nextClearBit(cursor) >= end;
    }

    public int getCursor() {
        return cursor;
    }

    public int getLength() {
        return length;
    }

    public void setLength(int newLength) {
        if (newLength < writtenPositions.length()) {
            writtenPositions.clear(newLength, writtenPositions.length());
        }
        cursor = Math.min(cursor, newLength);
        length = newLength;
    }

    public void seek(int pos) {
        cursor = pos;
    }

    @Override
    public String toString() {
        return "AbstractFileState[cursor=" + cursor + ", length=" + length + ", |writtenPositions|=" + writtenPositions.cardinality() + "]";
    }
}
