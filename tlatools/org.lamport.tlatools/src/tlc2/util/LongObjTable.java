// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:32 PST by lamport
//      modified on Mon Nov 26 15:41:48 PST 2001 by yuanyu

package tlc2.util;

import java.lang.reflect.Array;

@SuppressWarnings("unchecked")
public final class LongObjTable<T> {
    private final Class<T> clazz;
    private int count;
    private int length;
    private int thresh;
    private long[] keys;
    private T[] elems;

    public LongObjTable(Class<T> clazz, final int size) {
        this.clazz = clazz;
        this.keys = new long[size];
        this.elems = (T[]) Array.newInstance(clazz, size);
        this.count = 0;
        this.length = size;
        this.thresh = this.length / 2;
    }

    private void grow() {
        final long[] oldKeys = this.keys;
        final T[] oldElems = this.elems;
        this.count = 0;
        this.length = 2 * this.length + 1;
        this.thresh = this.length / 2;
        this.keys = new long[length];
        this.elems = (T[]) Array.newInstance(clazz, length);

        for (int i = 0; i < oldKeys.length; i++) {
            final T elem = oldElems[i];
            if (elem != null) this.put(oldKeys[i], elem);
        }
    }

    public int size() {
        return this.count;
    }

    public int put(final long k, final T elem) {
        if (count >= thresh) this.grow();
        int loc = ((int) k & 0x7FFFFFFF) % length;
        while (true) {
            if (this.elems[loc] == null) {
                this.keys[loc] = k;
                this.elems[loc] = elem;
                this.count++;
                return loc;
            } else if (this.keys[loc] == k) {
                this.elems[loc] = elem;
                return loc;
            }
            loc = (loc + 1) % length;
        }
    }

    public T get(final long k) {
        int loc = ((int) k & 0x7FFFFFFF) % length;
        while (true) {
            final T elem = this.elems[loc];
            if (elem == null) return null;
            if (this.keys[loc] == k) return elem;
            loc = (loc + 1) % length;
        }
    }

}
