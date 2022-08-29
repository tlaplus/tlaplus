// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:27 PST by lamport
//      modified on Thu Jan 10 18:33:42 PST 2002 by yuanyu

package tlc2.util;

import tlc2.output.EC;
import util.Assert;
import util.BufferedDataInputStream;
import util.BufferedDataOutputStream;
import util.FileUtil;

import java.io.File;

/**
 * Alternative implementation. Currently not used
 * <p>
 * This implementation is likely to have never worked and should be regarded as
 * a sketch for a how a concurrent implementation could look like. For the
 * moment, {@link SynchronousDiskIntStack} does the job just fine. Albeit - as
 * the name suggests - in a synchronous fashion.
 */
public final class DiskIntStack implements IntStack {
    private static final int BufSize = 16384;
    private final String filePrefix;
    private final Reader reader;
    private final Writer writer;
    private long size;
    private File poolFile;
    private int[] buf1, buf2, buf, rwbuf;
    private int index;
    private int hiPool;
    private boolean isIdle;

    public DiskIntStack(final String diskdir, final String name) {
        this.size = 0;
        this.buf1 = new int[BufSize];
        this.buf2 = new int[BufSize];
        this.rwbuf = new int[BufSize];
        this.buf = this.buf1;
        this.index = 0;
        this.hiPool = 0;
        this.isIdle = true;
        this.filePrefix = diskdir + FileUtil.separator + name;
        this.poolFile = null;
        this.reader = new Reader();
        this.writer = new Writer();
        this.reader.start();
        this.writer.start();
    }

    /* Return the number of items on the stack. */
    @Override
    public long size() {
        return this.size;
    }

    /* Push an integer onto the stack.  */
    @Override
    public synchronized void pushInt(final int x) {
        if (this.index == BufSize && this.buf == this.buf2) {
            // need to flush buf1 to disk
            try {
                while (!this.isIdle) this.wait();
                this.buf = this.rwbuf;
                this.rwbuf = this.buf1;
                this.poolFile = new File(this.filePrefix + this.hiPool++);
                this.isIdle = false;
                this.writer.notify();
                this.buf1 = this.buf2;
                this.buf2 = this.buf;
                this.index = 0;
            } catch (final Exception e) {
                Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES, new String[]{"stack", e.getMessage()});
            }
        }
        this.buf[this.index++] = x;
        this.size++;
    }

    /* Push a long integer onto the stack.  */
    @Override
    public synchronized void pushLong(final long x) {
        this.pushInt((int) (x & 0xFFFFFFFFL));
        this.pushInt((int) (x >>> 32));
    }

    /* Pop the integer on top of the stack.  */
    @Override
    public synchronized int popInt() {
        if (this.buf == this.buf1 && this.index < BufSize / 2 && this.hiPool != 0) {
            // need to fill buf1 from disk
            try {
                while (!this.isIdle) this.wait();
                this.buf = this.rwbuf;
                this.rwbuf = this.buf2;
                this.hiPool--;
                if (this.hiPool > 0) {
                    this.poolFile = new File(this.filePrefix + (this.hiPool - 1));
                    this.isIdle = false;
                    this.reader.notify();
                }
                this.buf2 = this.buf1;
                this.buf1 = this.buf;
                this.buf = this.buf2;
            } catch (final Exception e) {
                Assert.fail(EC.SYSTEM_ERROR_READING_STATES, new String[]{"stack", e.getMessage()});
            }
        }
        this.size--;
        return this.buf[--this.index];
    }

    /* Pop the long integer on top of the stack.  */
    @Override
    public synchronized long popLong() {
        final long high = this.popInt();
        final long low = this.popInt();
        return (high << 32) | (low & 0xFFFFFFFFL);
    }

    /* (non-Javadoc)
     * @see tlc2.util.IntStack#reset()
     */
    @Override
    public void reset() {
        // TODO Auto-generated method stub
    }

    class Reader extends Thread {
        @Override
        public void run() {
            try {
                synchronized (this) {
                    while (!Thread.currentThread().isInterrupted()) {
                        while (DiskIntStack.this.poolFile == null) {
                            this.wait();
                        }

                        try(final BufferedDataInputStream bdis = FileUtil.newBdFIS(false, DiskIntStack.this.poolFile)){
                            final int len = DiskIntStack.this.rwbuf.length;
                            for (int i = 0; i < len; i++) {
                                DiskIntStack.this.rwbuf[i] = bdis.readInt();
                            }
                        }

                        DiskIntStack.this.poolFile = null;
                        DiskIntStack.this.isIdle = true;
                        DiskIntStack.this.notify();
                    }
                }
            } catch (final Exception e) {
                Assert.fail(EC.SYSTEM_DISK_IO_ERROR_FOR_FILE, e);
            }
        }
    }

    class Writer extends Thread {
        @Override
        public void run() {
            try {
                synchronized (this) {
                    while (!Thread.currentThread().isInterrupted()) {
                        while (DiskIntStack.this.poolFile == null) {
                            this.wait();
                        }

                        try(final BufferedDataOutputStream bdos = FileUtil.newBdFOS(false, DiskIntStack.this.poolFile)){
                            for (final int j : DiskIntStack.this.buf) {
                                bdos.writeInt(j);
                            }
                        }

                        DiskIntStack.this.poolFile = null;
                        DiskIntStack.this.isIdle = true;
                        DiskIntStack.this.notify();
                    }
                }
            } catch (final Exception e) {
                Assert.fail(EC.SYSTEM_DISK_IO_ERROR_FOR_FILE, e);
            }
        }
    }
}
