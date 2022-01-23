// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:42 PST by lamport
//      modified on Sun Jul 29 23:32:03 PDT 2001 by yuanyu
package tlc2.util;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.NoSuchElementException;
import java.util.Vector;

/**
 * TODO it's unclear why we've written our own list implementation; we should consider using existing framework code for this;
 * 		we've also written our own "Vector" class in SANY...
 */
@SuppressWarnings("unchecked")
public class Vect<E> implements Cloneable, Serializable {
	private static final long serialVersionUID = 1L;

	
  private E[] elementData;
  private int elementCount;
         
  final class Enumerator implements Enumeration<E> {
    int index = 0;

    public final boolean hasMoreElements () {
      return (this.index < elementCount);
    }

    public final E nextElement() {
      return (E) elementData[index++];
    }
  }

  public Vect() { this(10); }

  public Vect(int initialCapacity) {
    this.elementCount = 0;
    if (initialCapacity == 0) {
      this.elementData = (E[]) new Object[0];
    }
    else {
      this.elementData = (E[]) new Object[initialCapacity];
    }
  }

  public Vect(final E[] array) {
    this(array.length);
    int sz = array.length;    
    for (int i = 0; i < sz; i++) {
      this.addElement(array[i]);
    }
  }

  public Vect(Vector<E> v) {
    this(v.size());
    int sz = v.size();    
    for (int i = 0; i < sz; i++) {
      this.addElement(v.elementAt(i));
    }
  }

  public final void addElement(E obj) {
    if (this.elementCount == this.elementData.length) {
      this.ensureCapacity(this.elementCount+1);
    }
    this.elementData[this.elementCount++] = obj;
  }

  public final Vect<E> concat(Vect<E> elems) {
    Vect<E> v = new Vect<>();
    for (int i = 0; i < this.elementCount; i++) {
      v.addElement(this.elementData[i]);
    }
    for (int i = 0; i < elems.size(); i++) {
      v.addElement(elems.elementAt(i));
    }
    return v;
  }

  public int capacity() { return this.elementData.length; }

  public Object clone() {
    Vect<E> v = new Vect<>(this.elementData.length);
    System.arraycopy(this.elementData, 0, v.elementData, 0, this.elementCount);
    v.elementCount = this.elementCount;
    return v;
  }

  public final boolean contains(Object elem) {
    return (this.indexOf(elem) != -1);
  }

  public final void copyInto(Object anArray[]) {
    System.arraycopy(this.elementData, 0, anArray, 0, this.elementCount);
  }

  public final E elementAt(int index) {
    return this.elementData[index];
  }

  @SuppressWarnings("rawtypes")
  public Enumeration<E> elements() { return new Vect.Enumerator(); }

  public final void ensureCapacity(int minCapacity) { 
    if (this.elementData.length < minCapacity) {
      int newCapacity = elementData.length + elementData.length;
      if (newCapacity < minCapacity) {
	newCapacity = minCapacity;
      }
      Object oldBuffer[] = elementData;
      elementData = (E[]) new Object[newCapacity];
      System.arraycopy( oldBuffer, 0, elementData, 0, elementCount);
    }
  }

  public final Object firstElement() {
    return this.elementData[0];
  }

  public final int indexOf(Object elem) { return this.indexOf(elem, 0); }

  public final int indexOf(Object elem, int index) {
    for (int pos = index; pos < elementCount; pos++) {
      if (elem.equals(elementData[pos])) return pos;
    }
    return -1;
  }

  public final void insertElementAt(E obj, int index) {
    if (elementCount == elementData.length)
      ensureCapacity(elementCount+1);

    if ((index > elementCount) || (index < 0)) {
      throw new ArrayIndexOutOfBoundsException();
    }
    else if (index < elementCount) {
      System.arraycopy(elementData, index, elementData, index+1, elementCount-index);
    }

    elementData[index] = obj;
    elementCount++;
  }

  public final boolean isEmpty() { return (this.elementCount == 0); }

  public final Object lastElement() {
    return this.elementData[this.elementCount-1];
  }

  public final void removeLastElement() {
    if (this.elementCount == 0) {
      throw new NoSuchElementException();
    }
    this.elementCount--;
    this.elementData[this.elementCount] = null;
  }
  
  public final void setElementAt(E obj, int index)	{
    this.elementData[index] = obj;
  }

  public final void removeElementAt(int index) {
    for (int i = index+1; i < this.elementCount; i++) {
      this.elementData[i-1] = this.elementData[i];
    }
    this.elementCount--;
    this.elementData[this.elementCount] = null;
  }

  /* Remove all elements except the first cnt elements.  */
  public final void removeAll(int cnt) {
    this.elementCount = cnt;
  }
  
  public final Object pop() {
    Object elem = this.lastElement();
    this.removeLastElement();
    return elem;
  }

  public final void push(E elem) {
    this.addElement(elem);
  }
  
  public final int size() { return this.elementCount; }

  public final int hashCode() {
    int code = 0;
    for (int i = 0; i < this.elementCount; i++) {
      code ^= this.elementData[i].hashCode();
    }
    return code;
  }

  public final boolean equals(Object obj) {
    if (!(obj instanceof Vect)) return false;
    Vect<E> v = (Vect<E>)obj;
    if (v.size() != this.elementCount) return false;
    for (int i = 0; i < this.elementCount; i++) {
      if (!this.elementData[i].equals(v.elementAt(i))) return false;
    }
    return true;
  }
  
  public String toString() {  
    StringBuffer buf = new StringBuffer("{");
    if (this.size() != 0) {
      buf.append(this.elementAt(0).toString());
    }
    for (int i = 1; i < this.size(); i++) {
      buf.append(",");
      buf.append(this.elementAt(i).toString());
    }
    buf.append("}");
    return buf.toString();
  }

}
