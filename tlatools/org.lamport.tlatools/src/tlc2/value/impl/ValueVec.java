// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Tue  1 May 2007 at 13:40:06 PST by lamport
//      modified on Tue Aug 21 17:02:26 PDT 2001 by yuanyu

package tlc2.value.impl;

import tlc2.TLCGlobals;
import util.WrongInvocationException;

import java.io.Serializable;
import java.util.Collection;

public class ValueVec implements Cloneable, Serializable {
    private static final long serialVersionUID = 3328179603723089649L;
    private static final Value[] empty = new Value[0];
    private Value[] elementData;
    private int elementCount;

    public ValueVec() {
        this(10);
    }

    public ValueVec(final int initialCapacity) {
        this.elementCount = 0;
        if (initialCapacity == 0) {
            this.elementData = empty;
        } else {
            this.elementData = new Value[initialCapacity];
        }
    }

    public ValueVec(final Value[] elems) {
        this.elementData = elems;
        this.elementCount = elems.length;
    }

    public ValueVec(final Collection<Value> elems) {
        this(elems.size());
        for (final Value value : elems) {
            add(value);
        }
    }

    public final void addElementAt(final Value val, final int index) {
        this.elementData[index] = val;
        this.elementCount++;
    }

    public final void add(final Value val) {
        if (this.elementCount == this.elementData.length) {
            ensureCapacity(this.elementCount + 1);
        }
        this.elementData[this.elementCount++] = val;
    }

    public final void addElement1(final Value val) {
        if (this.elementCount == this.elementData.length) {
            ensureCapacity(this.elementCount + 1);
        }
        for (int i = 0; i < this.elementCount; i++) {
            final int cmp = this.elementData[i].compareTo(val);
            if (cmp == 0) return;
            if (cmp > 0) {
                System.arraycopy(this.elementData, i, this.elementData, i + 1, this.elementCount - i);
                this.elementData[i] = val;
                this.elementCount++;
                return;
            }
        }
        this.elementData[this.elementCount++] = val;
    }

    public final int capacity() {
        return elementData.length;
    }

    @Override
    public final Object clone() {
        final ValueVec v = new ValueVec(this.elementData.length);

        System.arraycopy(elementData, 0, v.elementData, 0, elementCount);
        v.elementCount = elementCount;
        return v;
    }

    public final boolean contains(final Value elem) {
        return (indexOf(elem) != -1);
    }

    public final void copyInto(final Value[] anArray) {
        System.arraycopy(elementData, 0, anArray, 0, elementCount);
    }

    public final Value get(final int index) {
        // Assert.check(index < this.elementCount);
        return this.elementData[index];
    }

    public final void ensureCapacity(final int minCapacity) {
        if (elementData.length >= TLCGlobals.setBound) {
            throw new WrongInvocationException("Attempted to construct a set with too many elements (>" +
                    TLCGlobals.setBound + ").");
        }
        if (elementData.length < minCapacity) {
            int newCapacity = elementData.length + elementData.length;
            if (newCapacity < minCapacity) {
                newCapacity = minCapacity;
            }
            if (newCapacity > TLCGlobals.setBound) {
                newCapacity = TLCGlobals.setBound;
            }
            final Value[] oldData = this.elementData;
            this.elementData = new Value[newCapacity];

            System.arraycopy(oldData, 0, elementData, 0, elementCount);
        }
    }

    public final Value firstElement() {
        return this.elementData[0];
    }

    public final int indexOf(final Value elem) {
        return indexOf(elem, 0);
    }

    public final int indexOf(final Value elem, final int index) {
        for (int pos = index; pos < elementCount; pos++) {
            if (elem.equals(elementData[pos])) return pos;
        }
        return -1;
    }

    public final void insertElementAt(final Value obj, final int index) {
        if (elementCount == elementData.length) {
            this.ensureCapacity(elementCount + 1);
        }
        System.arraycopy(elementData, index, elementData, index + 1, elementCount - index);
        elementData[index] = obj;
        elementCount++;
    }

    public final boolean isEmpty() {
        return (elementCount == 0);
    }

    public final Value lastElement() {
        return this.elementData[this.elementCount - 1];
    }

    public final void setElementAt(final Value obj, final int index) {
        this.elementData[index] = obj;
    }

    public final int size() {
        return this.elementCount;
    }

    /* Assume that the elements are sorted. */
    public final boolean search(final Value elem, final boolean sorted) {
        if (sorted) {
            int cmp, mid, low = 0, high = this.elementCount;
            while (low < high) {
                mid = (low + high) >> 1;
                cmp = elem.compareTo(this.elementData[mid]);
                if (cmp == 0) return true;
                if (cmp < 0) {
                    high = mid;
                } else {
                    low = mid + 1;
                }
            }
        } else {
            for (int i = 0; i < this.elementCount; i++) {
                if (this.elementData[i].equals(elem)) {
                    return true;
                }
            }
        }
        return false;
    }

    public final ValueVec sort(final boolean noDup) {
        int newCount = (this.elementCount == 0) ? 0 : 1;
        for (int i = 1; i < this.elementCount; i++) {
            final Value elem = this.elementData[i];
            int cmp = 0, idx = 0, low = 0, high = newCount;
            while (low < high) {
                idx = (low + high) >> 1;
                cmp = elem.compareTo(this.elementData[idx]);
                if (cmp == 0) break;
                if (cmp < 0) {
                    high = idx;
                } else {
                    low = idx + 1;
                }
            }
            if (cmp != 0 || !noDup) {
                idx = (cmp < 0) ? idx : idx + 1;
                if (newCount - idx >= 0)
                    System.arraycopy(this.elementData, idx, this.elementData, idx + 1, newCount - idx);
                this.elementData[idx] = elem;
                newCount++;
            }
        }
        this.elementCount = newCount;
        return this;
    }

    public final String toString() {
        final StringBuilder sb = new StringBuilder();

        sb.append("{");
        if (this.size() > 0) {
            sb.append(this.elementData[0].toString());
        }
        for (int pos = 1; pos < size(); pos++) {
            sb.append(", ");
            sb.append(this.elementData[pos].toString());
        }
        sb.append("}");
        return sb.toString();
    }

    public Value[] toArray() {
        final Value[] copy = new Value[elementCount];
        System.arraycopy(elementData, 0, copy, 0, elementCount);
        return copy;
    }

}
