// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:33 PST by lamport
//      modified on Mon Dec  4 16:20:19 PST 2000 by yuanyu
package tlc2.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Arrays;

import util.FileUtil;

public class LongVec implements Cloneable, Serializable {
	private static final long serialVersionUID = 2406899362740899071L;
	protected long[] elementData;
	protected int elementCount;

	public LongVec() { this(10); }

	public LongVec(int initialCapacity) {
		this.elementCount = 0;
		this.elementData = new long[initialCapacity];
	}

	private LongVec(final LongVec other) {
		this.elementCount = other.elementCount;
		this.elementData = Arrays.copyOfRange(other.elementData, 0, other.elementCount);
	}

	public final void addElement(long x) {
		if (this.elementCount == this.elementData.length) {
			ensureCapacity(this.elementCount + 1);
		}
		this.elementData[this.elementCount++] = x;
	}

	public final long elementAt(int index) {
		rangeCheck(index);
		return this.elementData[index];
	}
	
	public final long lastElement() {
		return this.elementData[elementCount - 1];
	}

	public final void removeElement(int index) {
		rangeCheck(index);
		this.elementData[index] = this.elementData[this.elementCount - 1];
		this.elementCount--;
	}

	private void rangeCheck(int index) {
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
    private String outOfBoundsMsg(int index) {
        return "Index: "+index+", Size: "+elementCount;
    }

	public final boolean isEmpty() {
		return this.elementCount == 0;
	}

	public final int size() {
		return this.elementCount;
	}

	private final void ensureCapacity(int minCapacity) {
		if (elementData.length < minCapacity) {
			int newCapacity = elementData.length + elementData.length;
			if (newCapacity < minCapacity) {
				newCapacity = minCapacity;
			}
			long oldBuffer[] = this.elementData;
			this.elementData = new long[newCapacity];

			System.arraycopy(oldBuffer, 0, elementData, 0, elementCount);
		}
	}

	public final void reset() { this.elementCount = 0; }

	private void readObject(ObjectInputStream ois)
			  throws IOException, ClassNotFoundException {
		this.elementCount = ois.readInt();
		this.elementData = new long[this.elementCount];
		for (int i = 0; i < this.elementCount; i++) {
			this.elementData[i] = ois.readLong();
		}
	}

	private void writeObject(ObjectOutputStream oos) throws IOException {
		oos.writeInt(this.elementCount);
		for (int i = 0; i < this.elementCount; i++) {
			oos.writeLong(this.elementData[i]);
		}
	}

	public final String toString() {
		StringBuffer sb = new StringBuffer();
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

	public static void main(String args[]) throws Exception {
		LongVec vec = new LongVec(1000);
		vec.addElement(1);
		vec.addElement(3);
		vec.addElement(5);
		System.err.println(vec.size());
		ObjectOutputStream oos = FileUtil.newOBFOS("XXX");
		oos.writeObject(vec);

		ObjectInputStream ois = FileUtil.newOBFIS("XXX");
		LongVec vec1 = (LongVec) ois.readObject();
		System.err.println(vec1.size());
		System.err.println(vec1.elementAt(0));
		System.err.println(vec1.elementAt(1));
		System.err.println(vec1.elementAt(2));
	}

	private LongVec reverse0() {
		int left = 0;
		int right = elementData.length - 1;

		while (left < right) {
			long temp = elementData[left];
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
		} catch (Exception e) {
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
			long x = elementData[i];
			if (filtered.elementCount == 0 || filtered.lastElement() != x) {
				filtered.addElement(x);
			}
		}
		this.elementCount = filtered.elementCount;
		this.elementData = filtered.elementData;
		return this;
	}

	public LongVec removeLastIf(long x) {
		if (this.elementCount > 0 && this.lastElement() == x) {
			this.elementCount = this.elementCount - 1;
		}
		return this;
	}
}
