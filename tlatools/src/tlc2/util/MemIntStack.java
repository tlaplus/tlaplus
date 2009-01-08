// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:33 PST by lamport
//      modified on Thu Jan 10 18:33:42 PST 2002 by yuanyu

package tlc2.util;

public final class MemIntStack {
  private int size;
  private int[] elems;
  
  public MemIntStack(String diskdir, String name) {
    this.size = 0;
    this.elems = new int[1024];
  }

  /* Return the number of items on the stack. */
  public final int size() { return this.size; }
  
  /* Push an integer onto the stack.  */
  public final synchronized void pushInt(int x) {
    if (this.size == this.elems.length) {
      int[] elems1 = new int[2*this.size];
      System.arraycopy(elems, 0, elems1, 0, this.size);
      this.elems = elems1;
    }
    this.elems[this.size] = x;
    this.size++;
  }
  
  /* Push a long integer onto the stack.  */
  public final synchronized void pushLong(long x) {
    this.pushInt((int)(x & 0xFFFFFFFFL));
    this.pushInt((int)(x >>> 32));
  }

  /* Pop the integer on top of the stack.  */
  public final synchronized int popInt() {
    return this.elems[--this.size];
  }

  /* Pop the long integer on top of the stack.  */
  public final synchronized long popLong() {
    long high = this.popInt();
    long low = this.popInt();
    return (high << 32) | (low & 0xFFFFFFFFL);
  }

  public final void reset() { this.size = 0; }
  
}
