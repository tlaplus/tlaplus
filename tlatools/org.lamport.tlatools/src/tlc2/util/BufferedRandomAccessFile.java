// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2024, Oracle and/or its affiliates.
// Last modified on Mon 30 Apr 2007 at 13:26:26 PST by lamport
//      modified on Mon Jun 19 14:28:04 PDT 2000 by yuanyu
package tlc2.util;

import java.io.File;
import java.io.IOException;

/**
 * A <code>BufferedRandomAccessFile</code> is like a
 * <code>RandomAccessFile</code>, but it uses a private buffer
 * so that most operations do not require a disk access.
 *
 * <p>This class is not thread safe.
 *
 * <p>Clients sometimes need to interact with the buffer:
 * <ul>
 *     <li>{@link #flush()} ensures that all previously-performed writes have
 *         really been written (the same way that {@link java.io.RandomAccessFile#write(byte[])}
 *         would write them).</li>
 *     <li>{@link #invalidateBufferedData()} ensures that all previously-performed
 *         writes through other file descriptors are now readable through this one.</li>
 * </ul>
 *
 * @author Allan Heydon
 */
public final class BufferedRandomAccessFile extends java.io.RandomAccessFile {
    // Increase 8k buffer to match modern day hardware? No!!! The implementation
    // discards the whole buffer each time it seeks to a position outside the
    // current buffer. It then creates a new buffer, which takes proportionally
    // longer with larger buffer sizes.
    static final int LogBuffSz = 13; // 8K buffer
    public static final int BuffSz = (1 << LogBuffSz);

    /**
     * A bitwise mask composed of leading ones followed by exactly {@link #LogBuffSz} zeros.  It can be used to quickly
     * round down to the nearest {@link #BuffSz}-aligned offset:
     * <pre>
     *     offset - (offset % BuffSz) == offset & BuffMask
     * </pre>
     */
    // NOTE: some bitwise trickery going on here!  Because BuffSz is a positive power of 2 and ints are represented in
    // twos-complement, simply negating BuffSz produces the mask we seek.  The actual integer value of the result is
    // irrelevant; we only care about the bits here.
    static final int BuffMask = -BuffSz;

    /* This implementation is based on the buffer implementation in
       Modula-3's "Rd", "Wr", "RdClass", and "WrClass" interfaces,
       with substantial modifications. */

    /**
     * True if unflushed bytes exist.
     * @see #flushBuffer()
     */
    private boolean dirty;

    /**
     * True iff the file is closed.
     */
    private boolean closed;

    /** Current length of the file. */
    private long length;

    /** Current position in the file. */
    private long curr;

    /** Offset of <code>buff[0]</code> in the file. */
    private long lo;

    /** Cache of the bytes at indexes <code>[lo, min(lo + BuffSz, length))</code>. */
    private final byte[] buff;

    /**
     * Cached value of <code>super.{@link #getFilePointer()}</code>.  Used to avoid
     * some calls to <code>super.{@link #seek(long)}</code>.
     */
    private long diskPos;

    /**
     * Value of the mark.
     * @see #mark()
     * @see #reset()
     */
    private long mark;

    /** Protects {@link #availBuffs} and {@link #numAvailBuffs}. */
    private static final Object mu = new Object();
    private static byte[][] availBuffs = new byte[100][];
    private static int numAvailBuffs = 0;

    /*
       This class has a TLA+ spec (BufferedRandomAccessFile.tla).
       The TLA+ spec describes formally how the class fields work
       and what invariants they need to satisfy.  A little less
       formally, here's the intuition.

       To describe the above fields, we introduce the following
       abstractions for the file "f":

         curr(f)  the current position in the file
            c(f)  the abstract contents of the file
         disk(f)  the contents of f's backing disk file
          ptr(f)  the file pointer of f's backing disk file
       closed(f)  true iff the file is closed

       "curr(f)" and "ptr(f)" are indexes. See getFilePointer(). They
       can be any natural number; the RAF API allows clients to seek
       past the end of the file.

       "c(f)" is a byte sequence. "c(f)" and "disk(f)" may differ
       if "c(f)" contains unflushed writes not reflected in "disk(f)".
       The flush operation has the effect of modifying "disk(f)" to
       make it identical to "c(f)".

       Define "BufferedIndexes" to be the inclusive-exclusive interval

           [f.lo, min(f.lo + BuffSz, f.length))

       A file is said to be *valid* if the following conditions
       hold:

       V1. The "closed", "curr", "length", and "diskPos" fields are
           correct:

           f.closed == closed(f)
           f.curr == curr(f)
           f.length == len(c(f))
           f.diskPos = ptr(f)

       V2. The current position is contained in the buffer:

           f.lo <= f.curr < f.lo + BuffSz

       V3. Any (possibly) unflushed characters are stored
           in "f.buff":

           forall i in BufferedIndexes:
             c(f)[i] == f.buff[i - f.lo]

       V4. For all characters not covered by V3, c(f) and
           disk(f) agree:

           forall i in [0, f.length):
             i not in BufferedIndexes =>
               c(f)[i] == disk(f)[i]

       V5. If the buffer contains bytes that should be flushed to the
           file then "f.dirty" is true.  Note that "f.dirty" can be
           true even when there are no bytes that must be flushed (for
           instance, if the client wrote the same bytes that are
           already present on disk).

           (exists i in BufferedIndexes: disk(f)[i] != f.buff[i - f.lo])
             => f.dirty

       CAUTION: The RandomAccessFile API allows clients to seek past
       the end of the file.  In such a state, reads always return
       EOF and writes expand the file with arbitrary data to be large
       enough to contain the written bytes.  Therefore, it is possible
       for the buffer to be past the end of the file (f.lo > f.length).
    */

    /**
     * Open a new <code>BufferedRandomAccessFile</code> on the
     * file named <code>name</code> in mode <code>mode</code>,
     * which should be "r" for reading only, or "rw" for reading
     * and writing.
     */
    public BufferedRandomAccessFile(File file, String mode) throws IOException {
        super(file, mode);
        synchronized (mu) {
            this.buff = (numAvailBuffs > 0) ? availBuffs[--numAvailBuffs] : new byte[BuffSz];
        }
        this.closed = false;
        this.init();
    }

    /**
     * Open a new <code>BufferedRandomAccessFile</code> on the
     * file named <code>name</code> in mode <code>mode</code>, 
     * which should be "r" for reading only, or "rw" for reading
     * and writing.
     *
     * @deprecated Avoid stringly-typed code; use {@link #BufferedRandomAccessFile(File, String)} instead.
     */
    @Deprecated
    public BufferedRandomAccessFile(String name, String mode) throws IOException {
        // Simon Z. replaced the original:
        //    super(name, mode);
        //    this.init();
        // with this.
        this(new File(name), mode);
    }

    /**
     * Initialize the private fields of the file so as to make it valid.
     */
    private void init() throws IOException {
        this.dirty = false;
        this.lo = 0;
        this.curr = 0;
        this.diskPos = 0L;
        this.length = super.length();
        fillBuffer();
    }

    /**
     * Require that the file is open for use.
     *
     * @throws IOException if {@link #closed} is true
     */
    private void requireOpenFile() throws IOException {
        if (this.closed) {
            throw new IOException("File handle closed");
        }
    }

    /**
     * Invalidate any buffered data so that subsequent reads will go to disk.  Clients will typically call this when
     * they know that the on-disk contents have been altered through a different file descriptor and they need to
     * observe those writes through this one.
     *
     * <p>If this object has any buffered writes, this call will flush them to disk ({@link #flush()}).
     *
     * @throws IOException if an I/O error occurs flushing buffered writes
     */
    public void invalidateBufferedData() throws IOException {
        flush();

        // To preserve this class's invariants, we can't just clear the buffer; we also need to refill the
        // buffer from disk.
        fillBuffer();
    }

    @Override
    public void close() throws IOException {
        try {
            if (!this.closed) {
                this.flush();
                synchronized (mu) {
                    // grow "availBuffs" array if necessary
                    if (numAvailBuffs >= availBuffs.length) {
                        byte[][] newBuffs = new byte[numAvailBuffs + 10][];
                        System.arraycopy(availBuffs, 0, newBuffs, 0, numAvailBuffs);
                        availBuffs = newBuffs;
                    }
                    availBuffs[numAvailBuffs++] = this.buff;
                }
            }
        } finally {
            this.closed = true;
            super.close();
        }
    }

    /**
     * Flush any bytes in the file's buffer that have not
     * yet been written to disk. If the file was created
     * read-only, this method is a no-op.
     */
    public void flush() throws IOException {
        requireOpenFile();
        this.flushBuffer();
    }

    /**
     * Flush any dirty bytes in the buffer to disk.  Sets {@link #dirty} to <code>false</code>.
     *
     * @return true iff any disk writes were performed
     */
    private boolean flushBuffer() throws IOException {
        if (this.dirty) {
            // Assert.check(this.curr > this.lo);
            int len = (int)Math.min(this.length - this.lo, BuffSz);
            if (len > 0) {
                assert super.getFilePointer() == diskPos;
                if (this.diskPos != this.lo) {
                    super.seek(this.lo);
                }
                super.write(this.buff, 0, len);
                this.diskPos = this.lo + len;
            }
            this.dirty = false;
            return true;
        }
        return false;
    }

    /**
     * Restore invariant V3 by reading bytes into {@link #buff} starting from
     * <code>super.{@link #getFilePointer()}</code>.  Call this after changing
     * {@link #lo}.
     *
     * <p>Since this method clobbers the contents of {@link #buff}, callers
     * must be careful to ensure that there are no unflushed bytes (i.e.
     * {@link #dirty} is <code>false</code>). See {@link #flushBuffer()}.
     */
    private void fillBuffer() throws IOException {
        assert !dirty && diskPos == super.getFilePointer();

        // Ensure that we are reading from the correct point in the underlying file.
        if (diskPos != lo) {
            super.seek(lo);
            diskPos = lo;
        }

        // Read until the buffer is full or EOF.
        int cnt = 0;
        int rem = this.buff.length;
        while (rem > 0) {
            int n = super.read(this.buff, cnt, rem);
            if (n < 0) {
                break; // EOF
            }
            cnt += n;
            rem -= n;
        }

        // Update "this.diskPos" due to super.read() calls.
        this.diskPos += cnt;

        // There is a subtle case to consider as this method exits.  Suppose that:
        // 1. We didn't fill the buffer because we hit EOF (i.e. length < lo + BuffSz).
        // 2. The client calls seek() to jump forward, followed by write() to write a byte later in the buffer.
        //
        // Then the unset part of buff (represented by "*" below) can actually matter:
        //
        //                 length was 4 when fillBuffer() was called
        //                   v
        //     buff = [A B C D * * * * ...]
        //            >>>>>>>>>>>>>> ^
        //            seek(7)      write(0xFF)
        //
        // In that case, the file must be extended to contain the write, and the unset part of the buffer becomes part
        // of the official file contents.  Fortunately the RandomAccessFile contract gives us an out: when the file is
        // extended in this way, the unwritten portion can be filled with arbitrary data.  Therefore, we do not need to
        // do anything to the unset parts of buff.
        //
        // It is tempting to offer a slightly stronger contract by zero-filling the unset part of "buff":
        //
        //     Arrays.fill(this.buff, cnt, BuffSz, (byte)0);
        //
        // But do not be tempted!  That call incurs a performance penalty WITHOUT OFFERING A STRONGER CONTRACT!  There
        // are still cases where we rely on "super" to extend the file---meaning we inherit the weakest possible
        // contract from RandomAccessFile.  In particular, this happens when extending the file using setLength() or
        // when the client makes a giant forward seek followed by a write.
    }

    @Override
    public void seek(long pos) throws IOException {
        requireOpenFile();
        this.seeek(pos); // ignore boolean result
    }

    /**
     * Extends this.seek(long) by return if a page has been read (used for statistics).
     *
     * @return true iff data was read from disk
     */
    // NOTE: a call to seeek(this.curr) suffices to restore invariant V2 after this.curr changes.
    //TODO come up with better name for seeek %)
    public boolean seeek(long pos) throws IOException {
        // Assert.check(!this.closed);
        this.curr = pos;
        if (pos < this.lo || pos >= this.lo + BuffSz) {
            // seeking outside of current buffer -- flush and read
            this.flushBuffer();
            this.lo = pos & BuffMask; // start at BuffSz boundary
            this.fillBuffer();
            return true;
        }
        return false;
    }

    @Override
    public long getFilePointer() throws IOException {
        requireOpenFile();
        return this.curr;
    }

    @Override
    public long length() throws IOException {
        requireOpenFile();
        return this.length;
    }

    /**
     * Truncate or extend the file to the desired length.
     *
     * <p>This method behaves exactly like {@link java.io.RandomAccessFile#setLength(long)}, but fully constrains the
     * behavior of the file pointer: after this call, {@link #getFilePointer()} will be the minimum of the old file
     * pointer and the new file length.
     *
     * @param newLength    The desired length of the file
     * @throws IOException If an I/O error occurs
     */
    @Override
    public void setLength(long newLength) throws IOException {
        requireOpenFile();

        // Per docs:
        //  > If the present length of the file as returned by the length method is greater than the newLength argument
        //  > then the file will be truncated. In this case, if the file offset as returned by the getFilePointer
        //  > method is greater than newLength then after this method returns the offset will be equal to newLength.
        //
        // In practice, RandomAccessFile actually moves the pointer if getFilePointer > newLength, regardless of
        // whether the file was truncated or extended.
        super.setLength(newLength);
        this.length = newLength;

        // In theory, we should only have to update `this.diskPos` when `this.diskPos > newLength` (see note above).
        // But, because the RandomAccessFile docs are vague on this point, let's be careful.
        this.diskPos = super.getFilePointer();

        // Because the RandomAccessFile docs are vague, we have a bit of freedom here (see note above).  But let's do
        // exactly what we observed in practice (Java 11 and 21, April 2024): set `curr` to `min(curr, newLength)`.
        //
        // Note that there are two reasons why the obvious-looking call `seek(diskPos)` would be incorrect:
        //  1. We would inherit the underspecification mentioned above regarding the file pointer.  We have an
        //     opportunity to refine that specification with something more precise.
        //  2. Since `diskPos` was not necessarily in sync with `curr` at the start of this method, it is not likely
        //     to be in sync at this point either:
        //
        //           curr    diskPos
        //           v       v
        //          [A B C D * * * * ...]
        //
        //          setLength(3)
        //
        //           curr  diskPos
        //           v     v
        //          [A B C * * * * * ...]
        if (this.curr > newLength) {
            seek(newLength);
        }
    }

    /**
     * Restore relevant invariants (in particular V2) after increasing {@link #curr}.
     *
     * @throws IOException if some I/O operation fails
     */
    private void restoreInvariantsAfterIncreasingCurr() throws IOException {
        // NOTE: there may be some micro-optimization opportunity available here by inlining `seeek` and removing
        // redundant checks and code.
        if (this.curr >= this.lo + BuffSz) {
            seeek(this.curr);
        }
    }

    @Override
    public int read() throws IOException {
        // NOTE: single-byte reads are common enough to justify having an optimized procedure for them.
        requireOpenFile();

        // Check for EOF
        if (this.curr >= this.length) {
            return -1;
        }

        // Read the next byte out of the cache.  Invariant V2 guarantees that this read is in-bounds.
        int result = Byte.toUnsignedInt(this.buff[(int)(this.curr - this.lo)]);
        ++this.curr;

        restoreInvariantsAfterIncreasingCurr();

        return result;
    }

    @Override
    public int read(byte[] b) throws IOException {
        return this.read(b, 0, b.length);
    }

    @Override
    public int read(byte[] b, int off, int len) throws IOException {
        requireOpenFile();

        if (len == 0) {
            return 0;
        }

        // Read what we can into "b"
        long numReadableWithoutSeeking = Math.min(this.lo + BuffSz, this.length) - this.curr;

        // Check for EOF
        if (numReadableWithoutSeeking <= 0) {
            return -1;
        }

        int numToRead = Math.min(len, (int)numReadableWithoutSeeking);
        int buffOff = (int)(this.curr - this.lo);
        System.arraycopy(this.buff, buffOff, b, off, numToRead);
        this.curr += numToRead;

        restoreInvariantsAfterIncreasingCurr();

        return numToRead;
    }

    public final int readShortNat() throws IOException {
        int res = this.readByte();
        if (res >= 0) {
            return res;
        }
        res = (res << 16) | (this.readByte() & 0xff);
        return -res;
    }

    public final int readNat() throws IOException {
        int res = this.readShort();
        if (res >= 0) {
            return res;
        }
        res = (res << 16) | (this.readShort() & 0xffff);
        return -res;
    }

    public final long readLongNat() throws IOException {
        long res = this.readInt();
        if (res >= 0) {
            return res;
        }
        res = (res << 32) | ((long)this.readInt() & 0xffffffffL);
        return -res;
    }

    @Override
    public void write(int b) throws IOException {
        // NOTE: single-byte writes are common enough to justify having an optimized procedure for them.
        requireOpenFile();

        // Write the byte into the buffer.  Invariant V2 guarantees that this write is in-bounds.
        this.buff[(int)(this.curr - this.lo)] = (byte)b;
        ++this.curr;
        this.dirty = true;

        // Compute the new length
        this.length = Math.max(this.length, this.curr);

        restoreInvariantsAfterIncreasingCurr();
    }

    @Override
    public void write(byte[] b) throws IOException {
        this.write(b, 0, b.length);
    }

    @Override
    public void write(byte[] b, int off, int len) throws IOException {
        requireOpenFile();
        assert super.getFilePointer() == diskPos;
        while (len > 0) {
            // NOTE: this implementation might be a little wasteful!  Because `writeAtMost` has to maintain
            // invariant V2, it will actually do reads from disk when the write crosses outside the current
            // buffer.  This could be improved by relaxing V2 during this loop (or potentially removing that
            // invariant entirely).
            int n = this.writeAtMost(b, off, len);
            off += n;
            len -= n;
            assert super.getFilePointer() == diskPos;
        }
    }

    /* Precondition: x is a non-negative short. */
    public final void writeShortNat(int x) throws IOException {
        if (x <= 0x7f) {
            this.writeByte((short)x);
        } else {
            this.writeShort(-x);
        }
    }

    /* Precondition: x is a non-negative int. */
    public final void writeNat(int x) throws IOException {
        if (x <= 0x7fff) {
            this.writeShort((short)x);
        } else {
            this.writeInt(-x);
        }
    }

    /* Precondition: x is a non-negative long. */
    public final void writeLongNat(long x) throws IOException {
        if (x <= 0x7fffffff) {
            this.writeInt((int)x);
        } else {
            this.writeLong(-x);
        }
    }

    /**
     * Write at most "len" bytes from "b" starting at position "off", and return the number of bytes written.
     */
    private int writeAtMost(byte[] b, int off, int len) throws IOException {
        int numWriteableWithoutSeeking = Math.min(len, (int)(this.lo + BuffSz - this.curr));
        assert numWriteableWithoutSeeking > 0;

        int buffOff = (int) (this.curr - this.lo);
        System.arraycopy(b, off, this.buff, buffOff, numWriteableWithoutSeeking);
        this.dirty = true;
        this.curr += numWriteableWithoutSeeking;
        this.length = Math.max(this.length, this.curr);

        restoreInvariantsAfterIncreasingCurr();

        return numWriteableWithoutSeeking;
    }

    /**
     * Resets the BufferedRandomAccessFile so it appears to be a pristine, empty file.
     * The previous content of the underlying disk file will be overwritten and the file pointer will be moved
     * to the beginning of the file.
     *
     * @throws IOException
     */
    public void reset() throws IOException {
        setLength(0);
        this.init();
    }

    public long getMark() {
        return this.mark;
    }

    public long mark() {
        final long oldMark = this.mark;
        this.mark = curr;
        return oldMark;
    }

    public void seekAndMark(long pos) throws IOException {
        this.mark = pos;
        this.seek(pos);
    }

}
