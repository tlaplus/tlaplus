// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:25:48 PST by lamport  
//      modified on Thu Feb  8 23:32:12 PST 2001 by yuanyu   

package tlc2.tool.queue;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import tlc2.value.ValueConstants;
import tlc2.value.impl.*;
import util.*;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Arrays;

/**
 * A {@link DiskByteArrayQueue} uses the local hard disc as a backing store for
 * states. An in-memory buffer of size {@link DiskByteArrayQueue}{@link #BufSize}
 */
public class DiskByteArrayQueue extends ByteArrayQueue {
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
    protected final ByteArrayPoolReader reader;
    protected final ByteArrayPoolWriter writer;
    /**
     * The SPC takes care of deleting swap files on the lower end of the range
     * (loPool, hiPool). It terminates, when the first checkpoint is written at
     * which point checkpointing itself takes care of removing obsolete swap
     * files.
     */
    protected final StatePoolCleaner cleaner;
    /* Fields */
    private final String filePrefix;
    protected byte[][] deqBuf, enqBuf;
    protected int deqIndex, enqIndex;
    private int loPool, hiPool, lastLoPool, newLastLoPool;
    private File loFile;

    // TESTING ONLY!
    DiskByteArrayQueue(final TLCState emptyState) throws IOException {
        this(Files.createTempDirectory("DiskByteArrayQueue").toFile().toString(), emptyState);
    }

    /* Constructors */
    public DiskByteArrayQueue(final String diskdir, final TLCState emptyState) {
        super(emptyState);
        this.deqBuf = new byte[BufSize][];
        this.enqBuf = new byte[BufSize][];
        this.deqIndex = BufSize;
        this.enqIndex = 0;
        this.loPool = 1;
        this.hiPool = 0;
        this.lastLoPool = 0;
        this.filePrefix = diskdir + FileUtil.separator;
        final File rFile = new File(this.filePrefix + 0);
        this.reader = new ByteArrayPoolReader(BufSize, rFile);
        this.reader.setDaemon(true);
        this.loFile = new File(this.filePrefix + this.loPool);
        this.reader.start();
        this.writer = new ByteArrayPoolWriter(BufSize, this.reader);
        this.writer.setDaemon(true);
        this.writer.start();
        this.cleaner = new StatePoolCleaner();
        this.cleaner.setDaemon(true);
        this.cleaner.start();
    }

    @Override
    final void enqueueInner(final byte[] state) {
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
    final byte[] dequeueInner() {
        if (this.deqIndex == this.deqBuf.length) {
            this.fillDeqBuffer();
        }
        return this.deqBuf[this.deqIndex++];
    }

    @Override
    byte[] peekInner() {
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
                final byte[][] buf = this.reader.getCache(this.deqBuf, this.loFile);
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

        try (final BufferedDataOutputStream vos = new BufferedDataOutputStream(filename)) {
            vos.writeLong(this.len);
            vos.writeInt(this.loPool);
            vos.writeInt(this.hiPool);
            vos.writeInt(this.enqIndex);
            vos.writeInt(this.deqIndex);
            for (int i = 0; i < this.enqIndex; i++) {
                vos.writeInt(this.enqBuf[i].length);
                vos.write(this.enqBuf[i]);
            }
            for (int i = this.deqIndex; i < this.deqBuf.length; i++) {
                vos.writeInt(this.deqBuf[i].length);
                vos.write(this.deqBuf[i]);
            }
        }

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

        try (final BufferedDataInputStream vis = new BufferedDataInputStream(filename)) {
            this.len = vis.readLong();
            this.loPool = vis.readInt();
            this.hiPool = vis.readInt();
            this.enqIndex = vis.readInt();
            this.deqIndex = vis.readInt();
            this.lastLoPool = this.loPool - 1;

            for (int i = 0; i < this.enqIndex; i++) {
                this.enqBuf[i] = new byte[vis.readInt()];
                vis.read(this.enqBuf[i]);
            }
            for (int i = this.deqIndex; i < this.deqBuf.length; i++) {
                this.deqBuf[i] = new byte[vis.readInt()];
                vis.read(this.deqBuf[i]);
            }
        }

        final File file = new File(this.filePrefix + this.lastLoPool);
        final boolean canRead = (this.lastLoPool < this.hiPool);
        this.reader.restart(file, canRead);
        final String pstr = Integer.toString(this.loPool);
        this.loFile = new File(this.filePrefix + pstr);
    }

    @Override
    public synchronized void close() {
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
    }

    /* (non-Javadoc)
     * @see tlc2.tool.queue.IStateQueue#delete()
     */
    @Override
    public void delete() {
        this.close();
        new File(this.filePrefix).delete();
    }

    private static final class ByteArrayPoolWriter extends Thread {

        private final ByteArrayPoolReader reader;  // the consumer if not null
        private byte[][] buf;
        private File poolFile;           // the file to be written

        public ByteArrayPoolWriter(final int bufSize, final ByteArrayPoolReader reader) {
            super("RawTLCStatePoolWriter");
            this.buf = new byte[bufSize][];
            this.poolFile = null;
            this.reader = reader;
        }

        /*
         * This method first completes the preceding write if not started.
         * It then notifies this writer to flush enqBuf to file. In practice,
         * we expect the preceding write to have been completed.
         */
        public synchronized byte[][] doWork(final byte[][] enqBuf, final File file)
                throws IOException {
            if (this.poolFile != null) {
                try (final BufferedDataOutputStream vos = new BufferedDataOutputStream(this.poolFile)) {
                    for (final byte[] bytes : this.buf) {
                        vos.writeInt(bytes.length);
                        vos.write(bytes);
                    }
                }
            }
            final byte[][] res = this.buf;
            this.buf = enqBuf;
            this.poolFile = file;
            this.notify();
            return res;
        }

        /* Spin waiting for the write to complete.  */
        public void ensureWritten() throws InterruptedException {
            synchronized (this) {
                while (this.poolFile != null) {
                    this.wait();
                }
            }
        }

        /**
         * Write "buf" to "poolFile". The objects in the queue are written
         * using Java's object serialization facilities.
         */
        @Override
        public void run() {
            try {
                synchronized (this) {
                    while (!Thread.currentThread().isInterrupted()) {
                        while (this.poolFile == null) {
                            this.wait();
                            // we are done without ever receiving a pool file
                            if (this.poolFile == null) {
                                return;
                            }
                        }
                        final BufferedDataOutputStream vos = new BufferedDataOutputStream(this.poolFile);
                        for (final byte[] bytes : this.buf) {
                            vos.writeInt(bytes.length);
                            vos.write(bytes);
                        }
                        vos.close();
                        this.poolFile = null;
                        this.notify();
                        if (this.reader != null) this.reader.wakeup();
                    }
                }
            } catch (final Exception e) {
                // Assert.printStack(e);
                MP.printError(EC.SYSTEM_ERROR_WRITING_POOL, e.getMessage(), e);
                throw new FatalException("SYSTEM_ERROR_WRITING_POOL", e);
            }
        }
    }

    private static final class ByteArrayPoolReader extends Thread {

        private byte[][] buf;
        private File poolFile;      // the file to be read
        private boolean isFull;     // true iff the buf is filled
        private boolean canRead;    // true iff the file can be read
        private boolean finished = false;
        public ByteArrayPoolReader(final int bufSize, final File file) {
            super("RawTLCStatePoolReader");
            this.buf = new byte[bufSize][];
            this.poolFile = file;
            this.isFull = false;
            this.canRead = false;
        }

        public synchronized void wakeup() {
            this.canRead = true;
            this.notify();
        }

        public synchronized void restart(final File file, final boolean canRead) {
            this.poolFile = file;
            this.isFull = false;
            this.canRead = canRead;
            this.notify();
        }

        /*
         * In the most common case, this method expects to see the buffer is
         * full, it returns its buffer and notifies this reader to read the
         * content of the file.
         */
        public synchronized byte[][] doWork(final byte[][] deqBuf, final File file)
                throws IOException {
            if (this.isFull) {
                assert this.poolFile == null : EC.SYSTEM_FILE_NULL;
                final byte[][] res = this.buf;
                this.buf = deqBuf;
                this.poolFile = file;
                this.isFull = false;      // <file, false>
                this.canRead = true;
                this.notify();
                return res;
            } else if (this.poolFile != null) {
                try (final BufferedDataInputStream vis = new BufferedDataInputStream(this.poolFile)) {
                    for (int i = 0; i < deqBuf.length; i++) {
                        deqBuf[i] = new byte[vis.readInt()];
                        vis.read(deqBuf[i]);
                    }
                }

                this.poolFile = file;     // <file, false>
                this.canRead = true;
                this.notify();
                return deqBuf;
            } else {
                try (final BufferedDataInputStream vis = new BufferedDataInputStream(this.poolFile)) {
                    for (int i = 0; i < deqBuf.length; i++) {
                        deqBuf[i] = new byte[vis.readInt()];
                        vis.read(deqBuf[i]);
                    }
                }

                return deqBuf;
            }
        }

        /*
         * Returns the cached buffer if filled. Otherwise, returns null.
         */
        public synchronized byte[][] getCache(final byte[][] deqBuf, final File file)
                throws IOException {
            if (this.isFull) {
                assert this.poolFile == null : EC.SYSTEM_FILE_NULL;
                final byte[][] res = this.buf;
                this.buf = deqBuf;
                this.poolFile = file;
                this.isFull = false;      // <file, false>
                this.canRead = false;
                return res;
            } else if (this.poolFile != null && this.canRead) {
                // this should seldom occur.
                try (final BufferedDataInputStream vis = new BufferedDataInputStream(this.poolFile)) {
                    for (int i = 0; i < deqBuf.length; i++) {
                        deqBuf[i] = new byte[vis.readInt()];
                        vis.read(deqBuf[i]);
                    }
                }

                // this.poolFile.delete();
                this.poolFile = file;    // <file, false>
                this.canRead = false;
                return deqBuf;
            }
            return null;
        }

        /**
         * Read the contents of "poolFile" into "buf". The objects in the
         * file are read using Java's object serialization facilities.
         */
        @Override
        public void run() {
            try {
                synchronized (this) {
                    while (!Thread.currentThread().isInterrupted()) {
                        while (this.poolFile == null || this.isFull || !this.canRead) {
                            this.wait();
                            if (this.finished) {
                                return;
                            }
                        }
                        final BufferedDataInputStream vis = new BufferedDataInputStream(this.poolFile);
                        for (int i = 0; i < this.buf.length; i++) {
                            this.buf[i] = new byte[vis.readInt()];
                            vis.read(this.buf[i]);
                        }
                        vis.close();
                        this.poolFile = null;
                        this.isFull = true;       // <null, true>
                    }
                }
            } catch (final Exception e) {
                // Assert.printStack(e);
                MP.printError(EC.SYSTEM_ERROR_READING_POOL, e.getMessage(), e);
                throw new FatalException("SYSTEM_ERROR_READING_POOL", e);
            }
        }

        public void setFinished() {
            finished = true;
        }
    }

    static final class ByteValueOutputStream implements IValueOutputStream, IDataOutputStream {

        private byte[] bytes;

        private int idx;

        public ByteValueOutputStream() {
            this.bytes = new byte[16]; // TLCState "header" already has 6 bytes.
            this.idx = 0;
        }

        private void ensureCapacity(final int minCap) {
            if (minCap - bytes.length > 0) {
                final int oldCap = bytes.length;
                int newCap = oldCap << 1; // double size
                if (newCap - minCap < 0) {
                    newCap = minCap;
                }
                bytes = Arrays.copyOf(bytes, newCap);
            }
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#writeShort(short)
         */
        @Override
        public void writeShort(final short s) {
            ensureCapacity(idx + 2);
            this.bytes[idx++] = (byte) ((s >>> 8) & 0xff);
            this.bytes[idx++] = (byte) (s & 0xff);
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#writeInt(int)
         */
        @Override
        public void writeInt(final int i) {
            ensureCapacity(idx + 4);
            this.bytes[idx++] = (byte) ((i >>> 24) & 0xff);
            this.bytes[idx++] = (byte) ((i >>> 16) & 0xff);
            this.bytes[idx++] = (byte) ((i >>> 8) & 0xff);
            this.bytes[idx++] = (byte) (i & 0xff);
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#writeLong(long)
         */
        @Override
        public void writeLong(final long l) {
            ensureCapacity(idx + 8);
            this.bytes[idx++] = (byte) ((l >>> 56) & 0xff);
            this.bytes[idx++] = (byte) ((l >>> 48) & 0xff);
            this.bytes[idx++] = (byte) ((l >>> 40) & 0xff);
            this.bytes[idx++] = (byte) ((l >>> 32) & 0xff);
            this.bytes[idx++] = (byte) ((l >>> 24) & 0xff);
            this.bytes[idx++] = (byte) ((l >>> 16) & 0xff);
            this.bytes[idx++] = (byte) ((l >>> 8) & 0xff);
            this.bytes[idx++] = (byte) (l & 0xff);
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#close()
         */
        @Override
        public void close() {
            // No-op
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#writeShortNat(short)
         */
        @Override
        public void writeShortNat(final short x) {
            if (x > 0x7f) {
                this.writeShort((short) -x);
            } else {
                this.writeByte((byte) x);
            }
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#writeNat(int)
         */
        @Override
        public void writeNat(final int x) {
            if (x > 0x7fff) {
                this.writeInt(-x);
            } else {
                this.writeShort((short) x);
            }
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#writeLongNat(long)
         */
        @Override
        public void writeLongNat(final long x) {
            if (x <= 0x7fffffff) {
                this.writeInt((int) x);
            } else {
                this.writeLong(-x);
            }
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#writeByte(byte)
         */
        @Override
        public void writeByte(final byte b) {
            ensureCapacity(idx + 1);
            this.bytes[idx++] = b;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#writeBoolean(boolean)
         */
        @Override
        public void writeBoolean(final boolean bool) {
            final byte b = (bool ? (byte) 1 : (byte) 0);
            this.writeByte(b);
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#getOutputStream()
         */
        @Override
        public IDataOutputStream getOutputStream() {
            return this;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueOutputStream#put(java.lang.Object)
         */
        @Override
        public int put(final Object obj) {
            return -1;
        }

        public byte[] toByteArray() {
            final byte[] copyOf = Arrays.copyOf(bytes, idx);
            idx = 0;
            return copyOf;
        }

        /* (non-Javadoc)
         * @see util.IDataOutputStream#writeString(java.lang.String)
         */
        @Override
        public void writeString(final String str) {
            final int length = str.length();
            ensureCapacity(idx + length);

            final char[] c = new char[length];
            str.getChars(0, length, c, 0);

            for (final char value : c) {
                this.bytes[idx++] = (byte) value;
            }
        }
    }

    static final class ByteValueInputStream implements ValueConstants, IValueInputStream, IDataInputStream {

        private final byte[] bytes;

        private int idx = 0;

        public ByteValueInputStream(final byte[] bytes) {
            this.bytes = bytes;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#read()
         */
        @Override
        public IValue read() throws IOException {
            final byte kind = this.readByte();

            switch (kind) {
                case BOOLVALUE -> {
                    return (this.readBoolean()) ? BoolValue.ValTrue : BoolValue.ValFalse;
                }
                case INTVALUE -> {
                    return IntValue.gen(this.readInt());
                }
                case STRINGVALUE -> {
                    return StringValue.createFrom(this);
                }
                case MODELVALUE -> {
                    return ModelValue.mvs[this.readShort()];
                }
                case INTERVALVALUE -> {
                    return new IntervalValue(this.readInt(), this.readInt());
                }
                case RECORDVALUE -> {
                    return RecordValue.createFrom(this);
                }
                case FCNRCDVALUE -> {
                    return FcnRcdValue.createFrom(this);
                }
                case SETENUMVALUE -> {
                    return SetEnumValue.createFrom(this);
                }
                case TUPLEVALUE -> {
                    return TupleValue.createFrom(this);
                }
                default ->
                        throw new WrongInvocationException("ValueInputStream: Can not unpickle a value of kind " + kind);
            }
        }

        private boolean readBoolean() {
            return (bytes[idx++] != 0);
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#readShort()
         */
        @Override
        public int readShort() {
            return (short) ((bytes[idx++] << 8) | (bytes[idx++] & 0xff));
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#readInt()
         */
        @Override
        public int readInt() {
            int res = bytes[idx++];
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            return res;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#readLong()
         */
        @Override
        public long readLong() {
            long res = bytes[idx++];
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            res <<= 8;
            res |= (bytes[idx++] & 0xff);
            return res;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#close()
         */
        @Override
        public void close() {
            // No-op
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#readNat()
         */
        @Override
        public int readNat() {
            int res = this.readShort();
            if (res >= 0) return res;
            res = (res << 16) | (this.readShort() & 0xFFFF);
            return -res;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#readShortNat()
         */
        @Override
        public short readShortNat() {
            final short res = this.readByte();
            if (res >= 0) return res;
            return (short) -((res << 8) | (this.readByte() & 0xFF));
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#readLongNat()
         */
        @Override
        public long readLongNat() {
            long res = this.readInt();
            if (res >= 0) return res;
            res = (res << 32) | (this.readInt() & 0xFFFFFFFFL);
            return -res;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#readByte()
         */
        @Override
        public byte readByte() {
            return bytes[idx++];
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#assign(java.lang.Object, int)
         */
        @Override
        public void assign(final Object obj, final int idx) {
            // No-op
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#getIndex()
         */
        @Override
        public int getIndex() {
            return -1;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#getInputStream()
         */
        @Override
        public IDataInputStream getInputStream() {
            return this;
        }

        /* (non-Javadoc)
         * @see tlc2.value.IValueInputStream#getValue(int)
         */
        @Override
        public UniqueString getValue(final int idx) {
            throw new WrongInvocationException("Not supported");
        }

        /* (non-Javadoc)
         * @see util.IDataInputStream#readString(int)
         */
        @Override
        public String readString(final int length) {
            final char[] s = new char[length];
            for (int i = 0; i < s.length; i++) {
                s[i] = (char) this.bytes[idx++];
            }
            return new String(s);
        }
    }

    private class StatePoolCleaner extends Thread {

        public int deleteUpTo;
        private volatile boolean finished = false;

        private StatePoolCleaner() {
            super("RawTLCStatePoolCleaner");
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
