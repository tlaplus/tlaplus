// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:34 PST by lamport
//      modified on Sun Aug 26 20:11:53 PDT 2001 by yuanyu

package tlc2.util;

public final class ObjLongTable<T> {
    private int count;
    private int length;
    private int thresh;
    private T[] keys;
    private long[] elems;

    @SuppressWarnings("unchecked")
    public ObjLongTable(final int size) {
        this.keys = (T[]) new Object[size];
        this.elems = new long[size];
        this.count = 0;
        this.length = size;
        this.thresh = this.length / 2;
    }

    @SuppressWarnings("unchecked")
    private void grow() {
        final Object[] oldKeys = this.keys;
        final long[] oldElems = this.elems;
        this.count = 0;
        this.length = 2 * this.length + 1;
        this.thresh = this.length / 2;
        this.keys = (T[]) new Object[this.length];
        this.elems = new long[this.length];
        for (int i = 0; i < oldKeys.length; i++) {
            final T key = (T) oldKeys[i];
            if (key != null) this.put(key, oldElems[i]);
        }
    }

    public int size() {
        return this.count;
    }

    public int put(final T k, final long elem) {
        if (count >= thresh) this.grow();
        int loc = (k.hashCode() & 0x7FFFFFFF) % this.length;
        while (true) {
            final Object key = this.keys[loc];
            if (key == null) {
                this.keys[loc] = k;
                this.elems[loc] = elem;
                this.count++;
                return loc;
            } else if (key.equals(k)) {
                this.elems[loc] = elem;
                return loc;
            }
            loc = (loc + 1) % this.length;
        }
    }

    public int add(final T k, final long elem) {
        if (count >= thresh) this.grow();
        int loc = (k.hashCode() & 0x7FFFFFFF) % this.length;
        while (true) {
            final Object key = this.keys[loc];
            if (key == null) {
                this.keys[loc] = k;
                this.elems[loc] = elem;
                this.count++;
                return loc;
            } else if (key.equals(k)) {
                this.elems[loc] += elem;
                return loc;
            }
            loc = (loc + 1) % this.length;
        }
    }

    public long get(final Object k) {
        int loc = (k.hashCode() & 0x7FFFFFFF) % length;
        while (true) {
            final Object key = this.keys[loc];
            if (key == null) return 0;
            if (key.equals(k)) return this.elems[loc];
            loc = (loc + 1) % length;
        }
    }

    /**
     * Merges the keys and longs of into this instance. If this instance already
     * contains an entry with a given key, the long values will be accumulated.
     */
    public ObjLongTable<T> mergeInto(final ObjLongTable<T> other) {
        T key;
        final ObjLongTable<T>.Enumerator<T> keys2 = other.keys();
        while ((key = keys2.nextElement()) != null) {
            add(key, other.get(key));
        }
        return this;
    }

    @SuppressWarnings("unchecked")
    public T[] toArray(T[] a) {
        a = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), count);
        final ObjLongTable<T>.Enumerator<T> keys2 = keys();
        T e;
        int i = 0;
        while ((e = keys2.nextElement()) != null) {
            a[i++] = e;
        }
        return a;
    }

    public Enumerator<T> keys() {
        return new Enumerator<>();
    }

    @SuppressWarnings("hiding")
    public final class Enumerator<T> {
        int index = 0;

        @SuppressWarnings("unchecked")
        public T nextElement() {
            while (this.index < keys.length) {
                if (keys[this.index] != null) {
                    return (T) keys[this.index++];
                }
                this.index++;
            }
            return null;
        }
    }
}
