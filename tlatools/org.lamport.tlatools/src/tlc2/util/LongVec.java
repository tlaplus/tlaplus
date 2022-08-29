// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:33 PST by lamport
//      modified on Mon Dec  4 16:20:19 PST 2000 by yuanyu
package tlc2.util;

import util.FileUtil;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Arrays;

public class LongVec implements Cloneable, Serializable {
    private static final long serialVersionUID = 2406899362740899071L;
    protected long[] elementData;
    protected int elementCount;

    public LongVec() {
        this(10);
    }

    public LongVec(final int initialCapacity) {
        this.elementCount = 0;
        this.elementData = new long[initialCapacity];
    }

    private LongVec(final LongVec other) {
        this.elementCount = other.elementCount;
        this.elementData = Arrays.copyOfRange(other.elementData, 0, other.elementCount);
    }

    public static void main(final String[] args) throws Exception {
        final LongVec vec = new LongVec(1000);
        vec.add(1);
        vec.add(3);
        vec.add(5);
        System.err.println(vec.size());
        try (final ObjectOutputStream oos = FileUtil.newOBFOS("XXX")) {
            oos.writeObject(vec);
        }

        try (final ObjectInputStream ois = FileUtil.newOBFIS("XXX")) {
            final LongVec vec1 = (LongVec) ois.readObject();
            System.err.println(vec1.size());
            System.err.println(vec1.get(0));
            System.err.println(vec1.get(1));
            System.err.println(vec1.get(2));
        }
    }

    public final void add(final long x) {
        if (this.elementCount == this.elementData.length) {
            ensureCapacity(this.elementCount + 1);
        }
        this.elementData[this.elementCount++] = x;
    }

    public final long get(final int index) {
        rangeCheck(index);
        return this.elementData[index];
    }

    public final long lastElement() {
        return this.elementData[elementCount - 1];
    }

    public final void removeIndexMovingLastElement(final int index) {
        rangeCheck(index);
        this.elementData[index] = this.elementData[this.elementCount - 1];
        this.elementCount--;
    }

    private void rangeCheck(final int index) {
        if (index >= elementCount) {
            throw new IndexOutOfBoundsException(outOfBoundsMsg(index));
        }
    }

    /**
     * Constructs an IndexOutOfBoundsException detail message.
     * Of the many possible refactorings of the error handling code,
     * this "outlining" performs best with both server and client VMs.
     */
    // Copied from java.util.ArrayList
    private String outOfBoundsMsg(final int index) {
        return "Index: " + index + ", Size: " + elementCount;
    }

    public final boolean isEmpty() {
        return this.elementCount == 0;
    }

    public final int size() {
        return this.elementCount;
    }

    private void ensureCapacity(final int minCapacity) {
        if (elementData.length < minCapacity) {
            int newCapacity = elementData.length + elementData.length;
            if (newCapacity < minCapacity) {
                newCapacity = minCapacity;
            }
            final long[] oldBuffer = this.elementData;
            this.elementData = new long[newCapacity];

            System.arraycopy(oldBuffer, 0, elementData, 0, elementCount);
        }
    }

    public final void clear() {
        this.elementCount = 0;
    }

    private void readObject(final ObjectInputStream ois)
            throws IOException, ClassNotFoundException {
        this.elementCount = ois.readInt();
        this.elementData = new long[this.elementCount];
        for (int i = 0; i < this.elementCount; i++) {
            this.elementData[i] = ois.readLong();
        }
    }

    private void writeObject(final ObjectOutputStream oos) throws IOException {
        oos.writeInt(this.elementCount);
        for (int i = 0; i < this.elementCount; i++) {
            oos.writeLong(this.elementData[i]);
        }
    }

    public final String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("<");
        if (this.elementCount != 0) {
            sb.append(this.elementData[0]);
        }
        for (int i = 1; i < this.elementCount; i++) {
            sb.append(", ");
            sb.append(this.elementData[i]);
        }
        sb.append(">");
        return sb.toString();
    }

    private LongVec reverse0() {
        int left = 0;
        int right = elementData.length - 1;

        while (left < right) {
            final long temp = elementData[left];
            elementData[left] = elementData[right];
            elementData[right] = temp;

            left++;
            right--;
        }
        return this;
    }

    public LongVec reverse() {
        try {
            return new LongVec(this).reverse0();
        } catch (final Exception e) {
            throw e;
        }
    }

    /**
     * Remove *consecutive* duplicates:
     * [1,2,2,1,1,3] -> [1,2,1,3]
     */
    public LongVec pack() {
        // so far only used to while printing a liveness error trace and thus not
        // performance critical. Once performance matters, we should do it in-place.
        final LongVec filtered = new LongVec(size());
        for (int i = 0; i < elementCount; i++) {
            final long x = elementData[i];
            if (filtered.elementCount == 0 || filtered.lastElement() != x) {
                filtered.add(x);
            }
        }
        this.elementCount = filtered.elementCount;
        this.elementData = filtered.elementData;
        return this;
    }

    public LongVec removeLastIf(final long x) {
        if (this.elementCount > 0 && this.lastElement() == x) {
            this.elementCount = this.elementCount - 1;
        }
        return this;
    }
}
