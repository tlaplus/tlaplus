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
/**
 * 
 * 
 * @version $Id$
 */
public class LongVec implements Cloneable, Serializable {
  private static final long serialVersionUID = 2406899362740899071L;
  private long[] elementData;
  private int elementCount;
         
  public LongVec() { this(10); }

  public LongVec(int initialCapacity) {
    this.elementCount = 0;
    this.elementData = new long[initialCapacity];
  }

  public final void addElement(long x) {
    if (this.elementCount == this.elementData.length) {
      ensureCapacity(this.elementCount+1);
    }
    this.elementData[this.elementCount++] = x;
  }
  
  public final void setElement(int index, long x) {
	  this.elementData[index] = x;
	  this.elementCount = ++elementCount % elementData.length + 1;
	  }

  public final long elementAt(int index) {
    return this.elementData[index];
  }

  public final void removeElement(int index) {
    this.elementData[index] = this.elementData[this.elementCount-1];
    this.elementCount--;
  }
  
  public final int size() { return this.elementCount; }
  
  public final void sort() {
	  Arrays.sort(elementData);
  }

  public final void ensureCapacity(int minCapacity) { 
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
    LongVec vec1 = (LongVec)ois.readObject();
    System.err.println(vec1.size());
    System.err.println(vec1.elementAt(0));
    System.err.println(vec1.elementAt(1));
    System.err.println(vec1.elementAt(2));
  }

}
