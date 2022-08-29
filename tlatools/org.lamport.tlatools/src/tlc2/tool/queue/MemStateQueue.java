// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:15:31 PST by lamport
//      modified on Mon Dec 18 22:56:08 PST 2000 by yuanyu

package tlc2.tool.queue;

import tlc2.output.EC;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import util.Assert;
import util.FileUtil;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

public final class MemStateQueue extends StateQueue {
    private static final int InitialSize = 4096;
    private final String diskdir;
    private final ITool tool;
    /* Fields  */
    private TLCState[] states;
    private int start;

    /**
     * TESTING ONLY!
     */
    MemStateQueue(final ITool tool) throws IOException {
        this(Files.createTempDirectory("MemStateQueue").toFile().toString(), tool);
    }

    public MemStateQueue(final String metadir, final ITool tool) {
        this.states = new TLCState[InitialSize];
        this.start = 0;
        this.diskdir = metadir;
        this.tool = tool;
    }

    @Override
    void enqueueInner(final TLCState state) {
        if (this.len > Integer.MAX_VALUE) {
            Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES, new String[]{"queue", "Amount of states exceeds internal storage"});
        }
        if (this.len == this.states.length) {
            // grow the array
            final TLCState[] newStates = new TLCState[getNewLength(this.len)];
            final int copyLen = this.states.length - this.start;
            System.arraycopy(this.states, this.start, newStates, 0, copyLen);
            System.arraycopy(this.states, 0, newStates, copyLen, this.start);
            this.states = newStates;
            this.start = 0;
        }
        final int last = (this.start + (int) this.len) % this.states.length;
        this.states[last] = state;
    }

    /**
     * @return The new capacity softly increased
     */
    private int getNewLength(final long oldLength) {
        return (int) Math.max(1, ((oldLength * 4) / 3 + 1));
    }

    @Override
    TLCState dequeueInner() {
        final TLCState res = this.states[this.start];
        this.states[this.start] = null;
        this.start = (this.start + 1) % this.states.length;
        return res;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.queue.StateQueue#peekInner()
     */
    @Override
    TLCState peekInner() {
        return this.states[this.start];
    }

    // Checkpoint.
    @Override
    public void beginChkpt() throws IOException {
        final String filename = this.diskdir + FileUtil.separator + "queue.tmp";
        final ValueOutputStream vos = new ValueOutputStream(filename);
        vos.writeInt((int) this.len);
        int index = this.start;
        for (int i = 0; i < this.len; i++) {
            this.states[index++].write(vos);
            if (index == this.states.length) index = 0;
        }
        vos.close();
    }

    @Override
    public void commitChkpt() throws IOException {
        final String oldName = this.diskdir + FileUtil.separator + "queue.chkpt";
        final File oldChkpt = new File(oldName);
        final String newName = this.diskdir + FileUtil.separator + "queue.tmp";
        final File newChkpt = new File(newName);
        if ((oldChkpt.exists() && !oldChkpt.delete()) ||
                !newChkpt.renameTo(oldChkpt)) {
            throw new IOException("MemStateQueue.commitChkpt: cannot delete " + oldChkpt);
        }
    }

    @Override
    public void recover() throws IOException {
        final String filename = this.diskdir + FileUtil.separator + "queue.chkpt";
        final ValueInputStream vis = new ValueInputStream(filename);
        this.len = vis.readInt();
        for (int i = 0; i < this.len; i++) {
            this.states[i] = tool.getEmptyState().createNewFromValueStream(vis);
        }
        vis.close();
    }
}
