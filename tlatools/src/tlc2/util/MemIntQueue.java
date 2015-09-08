// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:33 PST by lamport
//      modified on Mon Dec 18 22:56:08 PST 2000 by yuanyu

package tlc2.util;

import java.io.File;
import java.io.IOException;
import java.util.NoSuchElementException;

import util.BufferedDataInputStream;
import util.BufferedDataOutputStream;
import util.FileUtil;

public final class MemIntQueue extends MemBasedSet {
	private final static int InitialSize = 4096;

	private int start;
	private String diskdir;
	private String filename;

	public MemIntQueue(String metadir, String filename) {
		this(metadir, filename, InitialSize);
	}

	public MemIntQueue(String metadir, String filename, final int initialCapacity) {
		super(initialCapacity);
		this.start = 0;
		this.diskdir = metadir;
		this.filename = filename;
	}

	public final void enqueueInt(int elem) {
		if (this.size == this.elems.length) {
			// grow the array
			final int[] newElems = ensureCapacity(InitialSize);
			// copy old content to new array
			int copyLen = this.elems.length - this.start;
			System.arraycopy(this.elems, this.start, newElems, 0, copyLen);
			System.arraycopy(this.elems, 0, newElems, copyLen, this.start);
			this.elems = newElems;
			this.start = 0;
		}
		int last = (this.start + this.size) % this.elems.length;
		this.elems[last] = elem;
		this.size++;
	}

	public final void enqueueLong(long elem) {
		this.enqueueInt((int) (elem >>> 32));
		this.enqueueInt((int) (elem & 0xFFFFFFFFL));
	}

	public final int dequeueInt() {
		// Assert.check(this.len > 0);
		if (this.size < 1) {
			throw new NoSuchElementException();
		}
		int res = this.elems[this.start];
		this.size--;
		this.start = (this.start + 1) % this.elems.length;
		return res;
	}

	public final long dequeueLong() {
		long high = this.dequeueInt();
		long low = this.dequeueInt();
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
		long low = this.popInt();
		long high = this.popInt();
		return (high << 32) | (low & 0xFFFFFFFFL);
	}

	// Checkpoint.
	public final void beginChkpt() throws IOException {
		String tmpName = this.diskdir + FileUtil.separator + this.filename + ".tmp";
		BufferedDataOutputStream bos = new BufferedDataOutputStream(tmpName);
		bos.writeInt(this.size);
		int index = this.start;
		for (int i = 0; i < this.size; i++) {
			bos.writeInt(this.elems[index++]);
			if (index == this.elems.length)
				index = 0;
		}
		bos.close();
	}

	public final void commitChkpt() throws IOException {
		String oldName = this.diskdir + FileUtil.separator + this.filename + ".chkpt";
		File oldChkpt = new File(oldName);
		String newName = this.diskdir + FileUtil.separator + this.filename + ".tmp";
		File newChkpt = new File(newName);
		if ((oldChkpt.exists() && !oldChkpt.delete()) || !newChkpt.renameTo(oldChkpt)) {
			throw new IOException("MemStateQueue.commitChkpt: cannot delete " + oldChkpt);
		}
	}

	public final void recover() throws IOException {
		String chkptName = this.diskdir + FileUtil.separator + this.filename + ".chkpt";
		BufferedDataInputStream bis = new BufferedDataInputStream(chkptName);
		this.size = bis.readInt();
		for (int i = 0; i < this.size; i++) {
			this.elems[i] = bis.readInt();
		}
		bis.close();
	}

	/*
	 * The detailed formatter below can be activated in Eclipse's variable view
	 * by choosing "New detailed formatter" from the MemIntQueue context menu.
	 * Insert "MemIntQueue.DetailedFormatter.fpAndtidxAndptr(this);".
	 */
	public static class DetailedFormatter {

		// An Eclipse detailed formatter for when this Queue holds pairs of long
		// (fp) and int (tableau idx)
		public static String fpAndtidx(MemIntQueue aQueue) {
			final StringBuffer buf = new StringBuffer(aQueue.size / 3);
			for (int i = 0; i < aQueue.size; i += 3) {
				final long fp = ((long) aQueue.elems[i] << 32) | ((long) (aQueue.elems[i + 1]) & 0xFFFFFFFFL);
				buf.append("fp: " + fp);
				buf.append(" tidx: " + aQueue.elems[i + 2]);
				buf.append("\n");
			}
			return buf.toString();
		}

		// An Eclipse detailed formatter for when this Queue holds pairs of long
		// (fp), int (tableau idx) and long (disk graph pointer).
		public static String fpAndtidxAndptr(MemIntQueue aQueue) {
			final StringBuffer buf = new StringBuffer(aQueue.size / 5);
			for (int i = 0; i < aQueue.size; i += 5) {
				final long fp = ((long) aQueue.elems[i] << 32) | ((long) (aQueue.elems[i + 1]) & 0xFFFFFFFFL);
				buf.append("fp: " + fp);
				buf.append(" tidx: " + aQueue.elems[i + 2]);
				final long ptr = ((long) aQueue.elems[i + 3] << 32) | ((long) (aQueue.elems[i + 4]) & 0xFFFFFFFFL);
				buf.append(" ptr: " + ptr);
				buf.append("\n");
			}
			return buf.toString();
		}
	}
}
