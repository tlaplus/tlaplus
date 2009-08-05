// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Tue  1 May 2007 at 13:40:06 PST by lamport
//      modified on Tue Aug 21 17:02:26 PDT 2001 by yuanyu

package tlc2.value;

import java.io.Serializable;

import tlc2.TLCGlobals;
import util.WrongInvocationException;

public class ValueVec implements Cloneable, Serializable {
  private Value[] elementData;
  private int elementCount;
         
  static private final Value[] empty = new Value[0];

  public ValueVec() { this(10); }

  public ValueVec(int initialCapacity) {
    this.elementCount = 0;
    if (initialCapacity == 0) {
      this.elementData = empty;
    }
    else {
      this.elementData = new Value[initialCapacity];
    }
  }

  public ValueVec(Value[] elems) {
    this.elementData = elems;
    this.elementCount = elems.length;
  }
  
  public final void addElement(Value val) {
    if (this.elementCount == this.elementData.length) {
      ensureCapacity(this.elementCount+1);
    }
    this.elementData[this.elementCount++] = val;
  }

  public final void addElement1(Value val) {
    if (this.elementCount == this.elementData.length) {
      ensureCapacity(this.elementCount+1);
    }
    for (int i = 0; i < this.elementCount; i++) {
      int cmp = this.elementData[i].compareTo(val);
      if (cmp == 0) return;
      if (cmp > 0) {
	for (int j = this.elementCount-1; j >= i; j--) {
	  this.elementData[j+1] = this.elementData[j];
	}
	this.elementData[i] = val;
	this.elementCount++;
	return;
      }
    }
    this.elementData[this.elementCount++] = val;
  }

  public final int capacity() { return elementData.length; }

  public final Object clone() {
    ValueVec v = new ValueVec(this.elementData.length);
	
    System.arraycopy(elementData, 0, v.elementData, 0, elementCount);
    v.elementCount = elementCount;
    return v;
  }

  public final boolean contains(Value elem) {
    return (indexOf(elem) != -1);
  }

  public final void copyInto(Value anArray[]) {
    System.arraycopy(elementData, 0, anArray, 0, elementCount);
  }

  public final Value elementAt(int index) {
    // Assert.check(index < this.elementCount);
    return this.elementData[index];
  }

  public final void ensureCapacity(int minCapacity) {
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
      Value oldData[] = this.elementData;
      this.elementData = new Value[newCapacity];

      System.arraycopy(oldData, 0, elementData, 0, elementCount);
    }
  }

  public final Value firstElement() { return this.elementData[0]; }

  public final int indexOf(Value elem) { return indexOf(elem, 0); }

  public final int indexOf(Value elem, int index) {
    for (int pos = index; pos < elementCount; pos++) {
      if (elem.equals(elementData[pos])) return pos;
    }
    return -1;
  }

  public final void insertElementAt(Value obj, int index) {
    if (elementCount == elementData.length) {
      this.ensureCapacity(elementCount+1);
    }
    System.arraycopy(elementData, index, elementData, index+1, elementCount-index);
    elementData[index] = obj;
    elementCount++;
  }

  public final boolean isEmpty() { return (elementCount == 0); }

  public final Value lastElement() {
    return this.elementData[this.elementCount-1];
  }

  public final void setElementAt(Value obj, int index)	{
    this.elementData[index] = obj;
  }

  public final int size() { return this.elementCount; }

  /* Assume that the elements are sorted. */
  public final boolean search(Value elem, boolean sorted) {
    if (sorted) {
      int cmp = 0, mid = 0, low = 0, high = this.elementCount;
      while (low < high) {
	mid = (low + high) >> 1;
	cmp = elem.compareTo(this.elementData[mid]);
	if (cmp == 0) return true;
	if (cmp < 0) {
	  high = mid;
	}
	else {
	  low = mid + 1;
	}
      }
    }
    else {
      for (int i = 0; i < this.elementCount; i++) {
	if (this.elementData[i].equals(elem)) {
	  return true;
	}
      }
    }
    return false;
  }

  public final void sort(boolean noDup) {
    int newCount = (this.elementCount == 0) ? 0 : 1;
    for (int i = 1; i < this.elementCount; i++) {
      Value elem = this.elementData[i];
      int cmp = 0, idx = 0, low = 0, high = newCount;
      while (low < high) {
	idx = (low + high) >> 1;
	cmp = elem.compareTo(this.elementData[idx]);
	if (cmp == 0) break;
	if (cmp < 0) {
	  high = idx;
	}
	else {
	  low = idx + 1;
	}
      }
      if (cmp != 0 || !noDup) {
	idx = (cmp < 0) ? idx  : idx + 1;
	for (int j = newCount; j > idx; j--) {
	  this.elementData[j] = this.elementData[j-1];
	}
	this.elementData[idx] = elem;
	newCount++;
      }
    }
    this.elementCount = newCount;
  }
  
  public final String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("{");
    if (this.size() > 0) {
      sb = sb.append(this.elementData[0].toString());
    }
    for (int pos = 1; pos < size(); pos++) {
      sb = sb.append(", ");
      sb = sb.append(this.elementData[pos].toString());
    }
    sb.append("}");    
    return sb.toString();
  }

}
