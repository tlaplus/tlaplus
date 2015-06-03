// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:46 PST by lamport
//      modified on Sun Jul 29 23:09:54 PDT 2001 by yuanyu

package tlc2.tool.liveness;

/**
 * @see TableauNodePtrTable
 */
public class NodePtrTable {

	private int count;
	private int length;
	private int thresh;
	private long[] keys;
	private long[] elems;

	/**
	 * @param size
	 */
	public NodePtrTable(int size) {
		this.count = 0;
		this.length = size;
		this.thresh = (int) (size * 0.75);
		this.keys = new long[size];
		this.elems = new long[size];
		for (int i = 0; i < size; i++) {
			this.elems[i] = -1;
		}
	}

	/**
	 * Add <k, elem> into the table. If the table has already contained k,
	 * overwrite the old value.
	 */
	public final void put(long k, long elem) {
		if (this.count >= this.thresh) {
			this.grow();
		}
		int loc = ((int) k & 0x7FFFFFFF) % this.length;
		while (true) {
			if (this.elems[loc] == -1) {
				this.keys[loc] = k;
				this.elems[loc] = elem;
				this.count++;
				return;
			}
			if (this.keys[loc] == k) {
				this.elems[loc] = elem;
				return;
			}
			loc = (loc + 1) % this.length;
		}
	}

	/* Return k's location if the table contains k. Otherwise, return -1. */
	public final int getLoc(long k) {
		if (count >= thresh) {
			this.grow();
		}
		int loc = ((int) k & 0x7FFFFFFF) % this.length;
		while (true) {
			if (this.elems[loc] == -1) {
				return -1;
			}
			if (this.keys[loc] == k) {
				return loc;
			}
			loc = (loc + 1) % this.length;
		}
	}

	/* Return the value with key k. Otherwise, return -1. */
	public final long get(long k) {
		if (count >= thresh) {
			this.grow();
		}
		int loc = ((int) k & 0x7FFFFFFF) % this.length;
		while (true) {
			if (this.elems[loc] == -1) {
				return -1;
			}
			if (this.keys[loc] == k) {
				return this.elems[loc];
			}
			loc = (loc + 1) % this.length;
		}
	}

	public final long getByLoc(int loc) {
		return this.elems[loc];
	}

	public final long getKeyByLoc(int loc) {
		return this.keys[loc];
	}

	public final void putByLoc(long k, long elem, int loc) {
		this.keys[loc] = k;
		this.elems[loc] = elem;
	}

	public void resetElems() {
		for (int i = 0; i < this.keys.length; i++) {
			this.elems[i] &= 0x7FFFFFFFFFFFFFFFL;
		}
	}

	/* Double the table when the table is full by the threshhold. */
	private final void grow() {
		this.length = 2 * this.length + 1;
		this.thresh = (int) (this.length * 0.75);
		this.count = 0;
		long[] oldKeys = this.keys;
		long[] oldElems = this.elems;
		this.keys = new long[this.length];
		this.elems = new long[this.length];
		for (int i = 0; i < this.length; i++) {
			this.elems[i] = -1;
		}
		for (int i = 0; i < oldElems.length; i++) {
			long elem = oldElems[i];
			if (elem != -1) {
				this.put(oldKeys[i], elem);
			}
		}
	}

	public final int size() {
		return this.count;
	}

	public final int getSize() {
		return this.length;
	}
}
