// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:25:48 PST by lamport  
//      modified on Thu Feb  8 23:32:12 PST 2001 by yuanyu   

package tlc2.tool.queue;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.util.StatePoolReader;
import tlc2.util.StatePoolWriter;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import util.Assert;
import util.FatalException;
import util.FileUtil;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

/**
 * A {@link DiskStateQueue} uses the local hard disc as a backing store for
 * states. An in-memory buffer of size {@link DiskStateQueue}{@link #BufSize}
 */
public class DiskStateQueue extends StateQueue {
    // TODO dynamic bufsize based on current VM parameters?
    private static final int BufSize = Integer.getInteger(DiskStateQueue.class.getName() + ".BufSize", 8192);

    /*
     * Invariants: I1. Entries in deqBuf are in the indices: [deqIndex,
     * deqBuffer.length ) I2. Entries in enqBuf are in the indices: [ 0,
     * enqIndex ) I3. 0 <= deqIndex <= deqBuf.length, where deqIndex == 0 =>
     * buffer full deqIndex == deqBuf.length => buffer empty I4. 0 <= enqIndex
     * <= enqBuf.length, where enqIndex == 0 => buffer empty enqIndex ==
     * enqBuf.length => buffer full
     */
    protected final StatePoolReader reader;
    protected final StatePoolWriter writer;
    /**
     * The SPC takes care of deleting swap files on the lower end of the range
     * (loPool, hiPool). It terminates, when the first checkpoint is written at
     * which point checkpointing itself takes care of removing obsolete swap
     * files.
     */
    protected final StatePoolCleaner cleaner;
    /* Fields */
    private final String filePrefix;
    private final TLCState emptyState;
    protected TLCState[] deqBuf, enqBuf;
    protected int deqIndex, enqIndex;
    private int loPool, hiPool, lastLoPool, newLastLoPool;
    private File loFile;

    // TESTING ONLY!
    DiskStateQueue(TLCState emptyState) throws IOException {
        this(Files.createTempDirectory("DiskStateQueue").toFile().toString(), emptyState);
    }

    /* Constructors */
    public DiskStateQueue(final String diskdir, TLCState emptyState) {
        this.deqBuf = new TLCState[BufSize];
        this.enqBuf = new TLCState[BufSize];
        this.deqIndex = BufSize;
        this.enqIndex = 0;
        this.loPool = 1;
        this.hiPool = 0;
        this.lastLoPool = 0;
        this.filePrefix = diskdir + FileUtil.separator;
        final File rFile = new File(this.filePrefix + 0);
        this.reader = new StatePoolReader(BufSize, rFile, emptyState);
        this.reader.setDaemon(true);
        this.loFile = new File(this.filePrefix + this.loPool);
        this.reader.start();
        this.writer = new StatePoolWriter(BufSize, this.reader);
        this.writer.setDaemon(true);
        this.writer.start();
        this.cleaner = new StatePoolCleaner();
        this.cleaner.setDaemon(true);
        this.cleaner.start();
        this.emptyState = emptyState;
    }

    @Override
    final void enqueueInner(final TLCState state) {
        if (this.enqIndex == this.enqBuf.length) {
            // enqBuf is full; flush it to disk
            try {
                final String pstr = Integer.toString(this.hiPool);
                final File file = new File(this.filePrefix + pstr);
                this.enqBuf = this.writer.doWork(this.enqBuf, file);
                this.hiPool++;
                this.enqIndex = 0;
            } catch (final Exception e) {
                Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES,
                        new String[]{"queue", (e.getMessage() == null) ? e.toString() : e.getMessage()});
            }
        }
        this.enqBuf[this.enqIndex++] = state;
    }

    @Override
    final TLCState dequeueInner() {
        if (this.deqIndex == this.deqBuf.length) {
            this.fillDeqBuffer();
        }
        return this.deqBuf[this.deqIndex++];
    }

    /* (non-Javadoc)
     * @see tlc2.tool.queue.StateQueue#peekInner()
     */
    @Override
    TLCState peekInner() {
        if (this.deqIndex == this.deqBuf.length) {
            this.fillDeqBuffer();
        }
        return this.deqBuf[this.deqIndex];
    }

    private void fillDeqBuffer() {
        try {
            if (this.loPool + 1 <= this.hiPool) {
                // We are sure there are disk files.
                if (this.loPool + 1 >= this.hiPool) {
                    // potential read-write conflict on a file
                    this.writer.ensureWritten();
                }
                this.deqBuf = this.reader.doWork(this.deqBuf, this.loFile);
                this.deqIndex = 0;
                this.loPool++;
                final String pstr = Integer.toString(this.loPool);
                this.loFile = new File(this.filePrefix + pstr);
            } else {
                // We still need to check if a file is buffered.
                this.writer.ensureWritten();
                final TLCState[] buf = this.reader.getCache(this.deqBuf, this.loFile);
                if (buf != null) {
                    this.deqBuf = buf;
                    this.deqIndex = 0;
                    this.loPool++;
                    final String pstr = Integer.toString(this.loPool);
                    this.loFile = new File(this.filePrefix + pstr);
                } else {
                    // copy entries from enqBuf to deqBuf.
                    this.deqIndex = this.deqBuf.length - this.enqIndex;
                    System.arraycopy(this.enqBuf, 0, this.deqBuf, this.deqIndex, this.enqIndex);
                    this.enqIndex = 0;
                }
            }
            // Notify the cleaner to do its job unless its waits for more work
            // to pile up.
            if ((loPool - lastLoPool) > 100) { //TODO Take BufSize into account. It defines the disc file size.
                synchronized (this.cleaner) {
                    this.cleaner.deleteUpTo = loPool - 1;
                    this.cleaner.notifyAll();
                }
            }
        } catch (final Exception e) {
            Assert.fail(EC.SYSTEM_ERROR_READING_STATES, new String[]{"queue",
                    (e.getMessage() == null) ? e.toString() : e.getMessage()});
        }
    }

    /* Checkpoint. */
    @Override
    public final void beginChkpt() throws IOException {
        synchronized (this.cleaner) {
            // Checkpointing takes precedence over periodic cleaning
            // (cleaner would otherwise delete checkpoint files as it know
            // nothing of checkpoints).
            this.cleaner.finished = true;
            this.cleaner.notifyAll();
        }

        final String filename = this.filePrefix + "queue.tmp";
        final ValueOutputStream vos = new ValueOutputStream(filename);
        vos.writeLongNat(this.len);
        vos.writeInt(this.loPool);
        vos.writeInt(this.hiPool);
        vos.writeInt(this.enqIndex);
        vos.writeInt(this.deqIndex);
        for (int i = 0; i < this.enqIndex; i++) {
            this.enqBuf[i].write(vos);
        }
        for (int i = this.deqIndex; i < this.deqBuf.length; i++) {
            this.deqBuf[i].write(vos);
        }
        vos.close();
        this.newLastLoPool = this.loPool - 1;
    }

    @Override
    public final void commitChkpt() throws IOException {
        for (int i = this.lastLoPool; i < this.newLastLoPool; i++) {
            final String pstr = Integer.toString(i);
            final File oldPool = new File(this.filePrefix + pstr);
            if (!oldPool.delete()) {
                final String msg = "DiskStateQueue.commitChkpt: cannot delete " + oldPool;
                throw new IOException(msg);
            }
        }
        this.lastLoPool = this.newLastLoPool;
        final File oldChkpt = new File(this.filePrefix + "queue.chkpt");
        final File newChkpt = new File(this.filePrefix + "queue.tmp");
        if ((oldChkpt.exists() && !oldChkpt.delete()) || !newChkpt.renameTo(oldChkpt)) {
            final String msg = "DiskStateQueue.commitChkpt: cannot delete " + oldChkpt;
            throw new IOException(msg);
        }
    }

    @Override
    public final void recover() throws IOException {
        final String filename = this.filePrefix + "queue.chkpt";
        final ValueInputStream vis = new ValueInputStream(filename);
        this.len = vis.readInt();
        this.loPool = vis.readInt();
        this.hiPool = vis.readInt();
        this.enqIndex = vis.readInt();
        this.deqIndex = vis.readInt();
        this.lastLoPool = this.loPool - 1;

        for (int i = 0; i < this.enqIndex; i++) {
            this.enqBuf[i] = emptyState.createNewFromValueStream(vis);
        }
        for (int i = this.deqIndex; i < this.deqBuf.length; i++) {
            this.deqBuf[i] = emptyState.createNewFromValueStream(vis);
        }
        vis.close();
        final File file = new File(this.filePrefix + this.lastLoPool);
        final boolean canRead = (this.lastLoPool < this.hiPool);
        this.reader.restart(file, canRead);
        final String pstr = Integer.toString(this.loPool);
        this.loFile = new File(this.filePrefix + pstr);
    }

    @Override
    public synchronized void close() throws Exception {
        super.close();
        synchronized (this.writer) {
            this.writer.notifyAll();
        }
        synchronized (this.reader) {
            this.reader.setFinished();
            this.reader.notifyAll();
        }
        synchronized (this.cleaner) {
            this.cleaner.finished = true;
            this.cleaner.notifyAll();
        }

        this.reader.join();
        this.cleaner.join();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.queue.IStateQueue#delete()
     */
    @Override
    public void delete() throws Exception {
        this.close();
        new File(this.filePrefix).delete();
    }

    private class StatePoolCleaner extends Thread {

        public int deleteUpTo;
        private volatile boolean finished = false;

        private StatePoolCleaner() {
            super("TLCStatePoolCleaner");
        }

        /* (non-Javadoc)
         * @see java.lang.Thread#run()
         */
        @Override
        public void run() {
            try {
                synchronized (this) {
                    while (!this.finished) {
                        this.wait();
                        if (this.finished) {
                            return;
                        }

                        for (int i = lastLoPool; i < deleteUpTo; i++) {
                            final File oldPoolFile = new File(filePrefix + i);
                            if (!oldPoolFile.delete()) {
                                // No reason to terminate/kill TLC when the cleanup fails.
                                // Contrary to StatePoolReader/Write, cleanup is optional
                                // functionality whose purpose is to prevent the disc from
                                // filling up. If the cleaner fails, the user can still
                                // manually delete the files.
                                MP.printWarning(EC.SYSTEM_ERROR_CLEANING_POOL, oldPoolFile.getCanonicalPath());
                            }
                        }
                        lastLoPool = deleteUpTo;
                    }
                }
            } catch (final Exception e) {
                // Assert.printStack(e);
                MP.printError(EC.SYSTEM_ERROR_CLEANING_POOL, e.getMessage(), e);
                throw new FatalException("SYSTEM_ERROR_CLEANING_POOL", e);
            }
        }
    }
}
