// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:15:31 PST by lamport
//      modified on Mon Dec 18 22:56:08 PST 2000 by yuanyu

package tlc2.tool.queue;

import java.io.File;
import java.io.IOException;

import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import util.Assert;
import util.FileUtil;

public final class MemStateQueue extends StateQueue {
  private final static int InitialSize = 4096;

  /* Fields  */
  private TLCState[] states;
  private int start = 0;
  private String diskdir;
    
  public MemStateQueue(String metadir) {
    this.states = new TLCState[InitialSize];
    this.start = 0;
    this.diskdir = metadir;
  }
    
  final void enqueueInner(TLCState state) {
	if (this.len > Integer.MAX_VALUE) {
        Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES, "Amount of states exceeds internal storage");
	}
    if (this.len == this.states.length) {
      // grow the array
      TLCState[] newStates = new TLCState[getNewLength(this.len)];
      int copyLen = this.states.length - this.start;
      System.arraycopy(this.states, this.start, newStates, 0, copyLen);
      System.arraycopy(this.states, 0, newStates, copyLen, this.start);
      this.states = newStates;
      this.start = 0;
    }
    int last = (this.start + (int) this.len) % this.states.length;
    this.states[last] = state;
  }
    
  /**
   * @param oldLength
   * @return The new capacity softly increased
   */
  private int getNewLength(final long oldLength) {
      return (int) Math.max(1, ((oldLength * 4) / 3 + 1));
  }

  final TLCState dequeueInner() {
    TLCState res = this.states[this.start];
    this.states[this.start] = null;
    this.start = (this.start + 1) % this.states.length;
    return res;
  }

  // Checkpoint.
  public final void beginChkpt() throws IOException {
    String filename = this.diskdir + FileUtil.separator + "queue.tmp";
    ValueOutputStream vos = new ValueOutputStream(filename);
    vos.writeInt((int)this.len);
    int index = this.start;
    for (int i = 0; i < this.len; i++) {
      this.states[index++].write(vos);
      if (index == this.states.length) index = 0;
    }
    vos.close();
  }

  public final void commitChkpt() throws IOException {
    String oldName = this.diskdir + FileUtil.separator + "queue.chkpt";
    File oldChkpt = new File(oldName);
    String newName = this.diskdir + FileUtil.separator + "queue.tmp";
    File newChkpt = new File(newName);
    if ((oldChkpt.exists() && !oldChkpt.delete()) ||
	!newChkpt.renameTo(oldChkpt)) {
      throw new IOException("MemStateQueue.commitChkpt: cannot delete " + oldChkpt);
    }
  }
  
  public final void recover() throws IOException {
    String filename = this.diskdir + FileUtil.separator + "queue.chkpt";
    ValueInputStream vis = new ValueInputStream(filename);
    this.len = vis.readInt();
    for (int i = 0; i < this.len; i++) {
      this.states[i] = TLCState.Empty.createEmpty();
      this.states[i].read(vis);
    }
    vis.close();
  }

}
