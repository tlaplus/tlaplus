// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:33 PST by lamport
//      modified on Mon Dec 18 22:56:08 PST 2000 by yuanyu

package tlc2.util;

import util.BufferedDataInputStream;
import util.BufferedDataOutputStream;
import util.FileUtil;

import java.io.File;
import java.io.IOException;
import java.util.NoSuchElementException;

public final class MemIntQueue extends MemBasedSet {
    private static final int InitialSize = 4096;
    private final String diskdir;
    private final String filename;
    private int start;

    public MemIntQueue(final String metadir, final String filename) {
        this(metadir, filename, InitialSize);
    }

    public MemIntQueue(final String metadir, final String filename, final int initialCapacity) {
        super(initialCapacity);
        this.start = 0;
        this.diskdir = metadir;
        this.filename = filename;
    }

    public void enqueueInt(final int elem) {
        if (this.size == this.elems.length) {
            // grow the array
            final int[] newElems = ensureCapacity(InitialSize);
            // copy old content to new array
            final int copyLen = this.elems.length - this.start;
            System.arraycopy(this.elems, this.start, newElems, 0, copyLen);
            System.arraycopy(this.elems, 0, newElems, copyLen, this.start);
            this.elems = newElems;
            this.start = 0;
        }
        final int last = (this.start + this.size) % this.elems.length;
        this.elems[last] = elem;
        this.size++;
    }

    public void enqueueLong(final long elem) {
        this.enqueueInt((int) (elem >>> 32));
        this.enqueueInt((int) (elem & 0xFFFFFFFFL));
    }

    public int dequeueInt() {
        // Assert.check(this.len > 0);
        if (this.size < 1) {
            throw new NoSuchElementException();
        }
        final int res = this.elems[this.start];
        this.size--;
        this.start = (this.start + 1) % this.elems.length;
        return res;
    }

    public long dequeueLong() {
        final long high = this.dequeueInt();
        final long low = this.dequeueInt();
        return (high << 32) | (low & 0xFFFFFFFFL);
    }

    public int popInt() {
        // Assert.check(this.len > 0);
        if (this.size < 1) {
            throw new NoSuchElementException();
        }
        return this.elems[--this.size];
    }

    public long popLong() {
        final long low = this.popInt();
        final long high = this.popInt();
        return (high << 32) | (low & 0xFFFFFFFFL);
    }

    // Checkpoint.
    public void beginChkpt() throws IOException {
        final String tmpName = this.diskdir + FileUtil.separator + this.filename + ".tmp";
        try (final BufferedDataOutputStream bos = new BufferedDataOutputStream(tmpName)) {
            bos.writeInt(this.size);
            int index = this.start;
            for (int i = 0; i < this.size; i++) {
                bos.writeInt(this.elems[index++]);
                if (index == this.elems.length)
                    index = 0;
            }
        }
    }

    public void commitChkpt() throws IOException {
        final String oldName = this.diskdir + FileUtil.separator + this.filename + ".chkpt";
        final File oldChkpt = new File(oldName);
        final String newName = this.diskdir + FileUtil.separator + this.filename + ".tmp";
        final File newChkpt = new File(newName);
        if ((oldChkpt.exists() && !oldChkpt.delete()) || !newChkpt.renameTo(oldChkpt)) {
            throw new IOException("MemStateQueue.commitChkpt: cannot delete " + oldChkpt);
        }
    }

    public void recover() throws IOException {
        final String chkptName = this.diskdir + FileUtil.separator + this.filename + ".chkpt";
        try (final BufferedDataInputStream bis = new BufferedDataInputStream(chkptName)) {
            this.size = bis.readInt();
            for (int i = 0; i < this.size; i++) {
                this.elems[i] = bis.readInt();
            }
        }
    }

    /*
     * The detailed formatter below can be activated in Eclipse's variable view
     * by choosing "New detailed formatter" from the MemIntQueue context menu.
     * Insert "MemIntQueue.DetailedFormatter.fpAndtidxAndptr(this);".
     */
    public static class DetailedFormatter {

        // An Eclipse detailed formatter for when this Queue holds pairs of long
        // (fp) and int (tableau idx)
        public static String fpAndtidx(final MemIntQueue aQueue) {
            final StringBuilder buf = new StringBuilder(aQueue.size / 3);
            for (int i = 0; i < aQueue.size; i += 3) {
                final long fp = ((long) aQueue.elems[i] << 32) | ((aQueue.elems[i + 1]) & 0xFFFFFFFFL);
                buf.append("fp: ").append(fp);
                buf.append(" tidx: ").append(aQueue.elems[i + 2]);
                buf.append("\n");
            }
            return buf.toString();
        }

        // An Eclipse detailed formatter for when this Queue holds pairs of long
        // (fp), int (tableau idx) and long (disk graph pointer).
        public static String fpAndtidxAndptr(final MemIntQueue aQueue) {
            final StringBuilder buf = new StringBuilder(aQueue.size / 5);
            for (int i = 0; i < aQueue.size; i += 5) {
                final long fp = ((long) aQueue.elems[i] << 32) | ((aQueue.elems[i + 1]) & 0xFFFFFFFFL);
                buf.append("fp: ").append(fp);
                buf.append(" tidx: ").append(aQueue.elems[i + 2]);
                final long ptr = ((long) aQueue.elems[i + 3] << 32) | ((aQueue.elems[i + 4]) & 0xFFFFFFFFL);
                buf.append(" ptr: ").append(ptr);
                buf.append("\n");
            }
            return buf.toString();
        }
    }
}
