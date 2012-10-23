// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:39 PST by lamport
//      modified on Thu Jul 12 16:10:42 PDT 2001 by yuanyu

package tlc2.util;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Arrays;

public final class SetOfLong {
  private int count;
  private int length;
  private int thresh;
  private long table[];
  private boolean hasZero;

  public SetOfLong(int size) {
    this.table = new long[size];
    this.count = 0;
    this.length = size;
    this.thresh = length / 2;
    this.hasZero = false;
  }

  public SetOfLong(int size, float ignore) { this(size); }

  private final void grow() {
    long[] old = table;
    this.count = 0;
    this.length = 2 * this.length + 1;
    this.thresh = this.length / 2;
    this.table = new long[this.length];
    for (int i = 0; i < old.length; i++) {
      long k = old[i];
      if (k != 0) this.put(k);
    }
  }

  /**
   * Add k into the table. Return true iff the table has already
   * contained k.
   */
  public final boolean put(long k) {
    if (count >= thresh) this.grow();
    if (k == 0) {
      if (this.hasZero) return true;
      this.hasZero = true;
      this.count++;
      return false;
    }
    else {
      int loc = ((int)k & 0x7FFFFFFF) % this.length;
      while (true) {
	long ent = this.table[loc];
	if (ent == k) return true;
	if (ent == 0) {
	  table[loc] = k;
	  count++;
	  return false;
	}
	loc = (loc + 1) % this.length;
      }
    }
  }

  /* Return true iff the table contains k. */
  public final boolean contains(long k) {
    if (k == 0) {
      return this.hasZero;
    }
    else {
      int loc = ((int)k & 0x7FFFFFFF) % this.length;
      while (true) {
	long ent = this.table[loc];
	if (ent == k) return true;
	if (ent == 0) return false;
	loc = (loc + 1) % this.length;
      }
    }
  }

  public final int size() { return this.count; }

  public final long sizeof() { return 20 + (8 * this.length); }

  public final double checkFPs() {
    int cnt = 0;
    for (int i = 0; i < this.length; i++) {
      long x = this.table[i];
      if (x != 0) {
	this.table[cnt++] = this.table[i];
      }
    }
    Arrays.sort(this.table, 0, cnt);

    long dis = Long.MAX_VALUE;
    long x = 0;
    int i = 0;
    if (!this.hasZero && cnt > 0) {
      x = this.table[0];
      i = 1;
    }
    for (; i < cnt; i++) {
      dis = Math.min(dis, this.table[i]-x);
      x = this.table[i];
    }
    return (1.0/dis);
  }

  public final void beginChkpt(DataOutputStream dos) throws IOException {
    dos.writeInt(this.count);
    dos.writeInt(this.length);
    dos.writeInt(this.thresh);
    dos.writeBoolean(this.hasZero);
    for (int i = 0; i < this.length; i++) {
      long k = this.table[i];
      if (k != 0) dos.writeLong(k);
    }
  }

  public final void recover(DataInputStream dis) throws IOException {
    this.count = dis.readInt();
    this.length = dis.readInt();
    this.thresh = dis.readInt();
    this.hasZero = dis.readBoolean();
    this.table = new long[this.length];
    int num = this.hasZero ? this.count-1 : this.count;
    for (int i = 0; i < num; i++) {
      this.put(dis.readLong());
    }
  }
  
}
