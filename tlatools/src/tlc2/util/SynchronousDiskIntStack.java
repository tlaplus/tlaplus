/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.util;

import java.io.File;

import tlc2.output.EC;
import util.Assert;
import util.BufferedDataInputStream;
import util.BufferedDataOutputStream;
import util.FileUtil;

public class SynchronousDiskIntStack implements IntStack {

	public final static int BufSize = 8388608; // ~32mb
	private final static int BufSizeMax = BufSize << 5; // ~1024mb

	private final int bufSize;
	private final String filePrefix;
	
	private long size = 0L;
	private int index = 0;

	private int hiPool = 0;
	
	private int[] buf;

	public SynchronousDiskIntStack(String diskdir, String name) {
		this(diskdir, name, BufSize);
	}
	
	public SynchronousDiskIntStack(String diskdir, String name, int capacity) {
		// Hard-limit capacity to 1gb per page file
		capacity = Math.min(BufSizeMax, Math.max(capacity, BufSize));
		this.filePrefix = diskdir + FileUtil.separator + name;
		this.bufSize = capacity;
		this.buf = new int[capacity];
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IntStack#size()
	 */
	public long size() {
		return this.size;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IntStack#pushInt(int)
	 */
	public void pushInt(int x) {
		if (this.index == bufSize) {
			// flush to disk
			try {
				final File poolFile = new File(this.filePrefix + Integer.toString(this.hiPool));
				poolFile.deleteOnExit();
				final BufferedDataOutputStream bdos = FileUtil.newBdFOS(false, poolFile);
				final int len = buf.length;
				for (int i = 0; i < len; i++) {
					bdos.writeInt(buf[i]);
				}
				bdos.close();
				this.hiPool++;
				this.index = 0;
			} catch (Exception e) {
				Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES, new String[] { "stack", e.getMessage() });
			}
		}
		this.buf[this.index++] = x;
		this.size++;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IntStack#pushLong(long)
	 */
	public void pushLong(long x) {
		this.pushInt((int) (x & 0xFFFFFFFFL));
		this.pushInt((int) (x >>> 32));
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IntStack#popInt()
	 */
	public int popInt() {
		if (this.index == 0 && hasPool()) {
			// fill buffer
			try {
				final File poolFile = new File(this.filePrefix + Integer.toString(this.hiPool - 1));
				final BufferedDataInputStream bdis = FileUtil.newBdFIS(false, poolFile);
				final int len = buf.length;
				for (int i = 0; i < len; i++) {
					buf[i] = bdis.readInt();
				}
				bdis.close();
				this.hiPool--;
				this.index = len;
			} catch (Exception e) {
				Assert.fail(EC.SYSTEM_ERROR_WRITING_STATES, new String[] { "stack", e.getMessage() });
			}
		}
		this.size--;
		return this.buf[--this.index];
	}
	
	private boolean hasPool() {
		return this.hiPool >= 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IntStack#popLong()
	 */
	public long popLong() {
		long high = this.popInt();
		long low = this.popInt();
		return (high << 32) | (low & 0xFFFFFFFFL);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IntStack#reset()
	 */
	public void reset() {
		this.size = 0L;
		this.index = 0;

		this.hiPool = 0;
	}
}
