// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.value;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.zip.GZIPOutputStream;

import tlc2.TLCGlobals;
import util.BufferedDataOutputStream;

public final class ValueOutputStream {

  private final BufferedDataOutputStream dos;
  private final HandleTable handles;

  public ValueOutputStream(File file) throws IOException {
    if (TLCGlobals.useGZIP) {
      OutputStream os = new GZIPOutputStream(new FileOutputStream(file));
      this.dos = new BufferedDataOutputStream(os);
    }
    else {
      this.dos = new BufferedDataOutputStream(file);
    }
    this.handles = new HandleTable();
  }

  public ValueOutputStream(String fname) throws IOException {
    if (TLCGlobals.useGZIP) {
      OutputStream os = new GZIPOutputStream(new FileOutputStream(fname));
      this.dos = new BufferedDataOutputStream(os);
    }
    else {
      this.dos = new BufferedDataOutputStream(fname);
    }
    this.handles = new HandleTable();
  }

  public final void writeShort(short x) throws IOException {
	  this.dos.writeShort(x);
  }
  
  public final void writeInt(int x) throws IOException {
    this.dos.writeInt(x);
  }

  public final void writeLong(long x) throws IOException {
    this.dos.writeLong(x);
  }
  
  public final void close() throws IOException {
    this.dos.close();
  }
  
  /* Precondition: x is a non-negative short. */
  public final void writeShortNat(short x) throws IOException {
    if (x > 0x7f) {
      this.dos.writeShort((short) -x);
    }
    else {
      this.dos.writeByte((byte)x);
    }
  }

  /* Precondition: x is a non-negative int. */
  public final void writeNat(int x) throws IOException {
    if (x > 0x7fff) {
      this.dos.writeInt(-x);
    }
    else {
      this.dos.writeShort((short)x);
    }
  }

  /* Precondition: x is a non-negative long. */
  public final void writeLongNat(long x) throws IOException {
    if (x <= 0x7fffffff) {
      this.dos.writeInt((int)x);
    }
    else {
      this.dos.writeLong(-x);
    }
  }
	
	public final void writeByte(final byte b) throws IOException {
		this.dos.writeByte(b);
	}

	public final void writeBoolean(final boolean b) throws IOException {
		this.dos.writeBoolean(b);
	}

	public final BufferedDataOutputStream getOutputStream() {
		return dos;
	}

	/**
	 * Check if another TLCState - which is currently also being serialized to the
	 * same storage (i.e. disk file) - has/contains an identical Value. If yes, do
	 * not serialize the Value instance again but make this TLCState point to the
	 * Value instance previously serialized for the other TLCState. In other words,
	 * this is a custom-tailored compression/de-duplication mechanism for Value
	 * instances.
	 * <p>
	 * This approach only works because both TLCStates are serialized to the same
	 * storage and thus de-serialized as part of the same operation (same
	 * Value*Stream instance).
	 * <p>
	 * The purpose of this approach appears to be:
	 * <ul>
	 * <li>Reduce serialization efforts and storage size</li>
	 * <li>Reduce the number of Value instances created during de-serialization</li>
	 * <li>Allow identity comparison on Value instances (AFAICT not used by Value
	 * explicitly, just UniqueString) to speed up check. Value#equals internally
	 * likely uses identity comparison as first check.</li>
	 * </ul>
	 * <p>
	 * A disadvantage is the cost of maintaining the internal HandleTable which can
	 * grow to thousands of elements during serialization/de-serialization (in
	 * ValueInputStream). Since serialization suspends the DiskStateQueue and thus
	 * blocks tlc2.tool.Workers from exploring the state space, this might has
	 * adverse effects.
	 */
	public final int put(final Object obj) {
		return this.handles.put(obj);
	}
  
  private static class HandleTable {
    private int[] spine;
    private int[] next;
    private Object[] values;
    private int size;
    private int threshold;
    
    HandleTable() {
      this.spine = new int[17];
      Arrays.fill(spine, -1);
      this.next = new int[16];
      this.values = new Object[16];
      this.size = 0;
      this.threshold = (int)(this.spine.length * 0.75);
    }

// SZ Jul 13, 2009: not used
//    final int size() { return this.size; }
    
    final int put(Object val) {
      int index = (System.identityHashCode(val) & 0x7FFFFFFF) % this.spine.length;
      // lookup:
      for (int i = spine[index]; i >= 0; i = next[i]) {
	if (values[i] == val) { return i; }
      }
      // grow if needed:
      if (this.size >= this.next.length) {
	this.growEntries();
      }
      if (this.size >= this.threshold) {
	this.growSpine();
	index = (System.identityHashCode(val) & 0x7FFFFFFF) % this.spine.length;
      }
      // add val to the table:
      this.values[this.size] = val;
      this.next[this.size] = this.spine[index];
      this.spine[index] = this.size;
      this.size++;
      return -1;
    }

    private final void growEntries() {
      int newLength = this.next.length * 2;
      int[] newNext = new int[newLength];
      System.arraycopy(this.next, 0, newNext, 0, this.size);
      this.next = newNext;

      Object[] newValues = new Object[newLength];
      System.arraycopy(this.values, 0, newValues, 0, this.size);
      this.values = newValues;
    }

    private final void growSpine() {
      int len = (this.spine.length * 2) + 1;
      this.spine = new int[len];
      this.threshold = (int)(len * 0.75);
      Arrays.fill(this.spine, -1);
      for (int i = 0; i < this.size; i++) {
	int index = (System.identityHashCode(this.values[i]) & 0x7FFFFFFF) % len;
	this.next[i] = this.spine[index];
	this.spine[index] = i;
      }
    }
  }
}
