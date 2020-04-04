// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:40 PST by lamport
//      modified on Sun Dec  3 17:47:37 PST 2000 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;

public class TLCStateVec implements Cloneable, Serializable {
  private TLCState[] elementData;
  private int elementCount;
         
  public TLCStateVec() { this(10); }

  public TLCStateVec(int initialCapacity) {
    this.elementCount = 0;
    this.elementData = new TLCState[initialCapacity];
  }

  public final void addElement(TLCState x) {
    if (this.elementCount == this.elementData.length) {
      ensureCapacity(this.elementCount+1);
    }
    this.elementData[this.elementCount++] = x;
  }

  public final TLCState elementAt(int index) {
    return this.elementData[index];
  }

  public final int size() { return this.elementCount; }

  public final void ensureCapacity(int minCapacity) { 
    if (elementData.length < minCapacity) {
      int newCapacity = elementData.length + elementData.length;
      if (newCapacity < minCapacity) {
	newCapacity = minCapacity;
      }
      TLCState oldBuffer[] = this.elementData;
      this.elementData = new TLCState[newCapacity];

      System.arraycopy(oldBuffer, 0, elementData, 0, elementCount);
    }
  }

  private void readObject(ObjectInputStream ois)
  throws IOException, ClassNotFoundException {
    this.elementCount = ois.readInt();
    this.elementData = new TLCState[this.elementCount];
    for (int i = 0; i < this.elementCount; i++) {
      this.elementData[i] = (TLCState)ois.readObject();
    }
  }

  private void writeObject(ObjectOutputStream oos) throws IOException {
    oos.writeInt(this.elementCount);
    for (int i = 0; i < this.elementCount; i++) {
      oos.writeObject(this.elementData[i]);
    }
  }

}


