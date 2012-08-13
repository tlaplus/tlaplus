// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:26 PST by lamport
//      modified on Mon Jun 19 14:28:04 PDT 2000 by yuanyu
package tlc2.util;

/**
 * A <code>BufferedRandomAccessFile</code> is like a
 * <code>RandomAccessFile</code>, but it uses a private buffer
 * so that most operations do not require a disk access.<P>
 * 
 * Note: The operations on this class are unmonitored.
 * The code was written by Allan Heydon
 */

import java.io.File;
import java.io.IOException;
import java.math.BigInteger;

public final class BufferedRandomAccessFile extends java.io.RandomAccessFile {
	//TODO increase buffer to match modern day hardware?
	static final int LogBuffSz = 13; // 8K buffer
    public static final int BuffSz = (1 << LogBuffSz);
    static final int BuffMask = ~(BuffSz - 1);

    /* This implementation is based on the buffer implementation in
       Modula-3's "Rd", "Wr", "RdClass", and "WrClass" interfaces. */
    private boolean dirty;  // true iff unflushed bytes exist
    // SZ Feb 24, 2009: never read
    // private boolean closed; // true iff the file is closed
    private long curr;      // current position in file
    private long lo, hi;    // bounds on characters in "buff"
    private byte[] buff;    // local buffer
    private long maxHi;     // this.lo + this.buff.length
    private boolean hitEOF; // buffer contains last file block?
    private long diskPos;   // disk position
    
    private static Object mu = new Object(); // protects the following fields
    private static byte[][] availBuffs = new byte[100][];
    private static int numAvailBuffs = 0;

    /* To describe the above fields, we introduce the following
       abstractions for the file "f":

          len(f)  the length of the file
         curr(f)  the current position in the file
            c(f)  the abstract contents of the file
         disk(f)  the contents of f's backing disk file
       closed(f)  true iff the file is closed

       "curr(f)" is an index in the closed interval [0, len(f)].
       "c(f)" is a character sequence of length "len(f)". "c(f)"
       and "disk(f)" may differ if "c(f)" contains unflushed
       writes not reflected in "disk(f)". The flush operation has
       the effect of making "disk(f)" identical to "c(f)".

       A file is said to be *valid* if the following conditions
       hold:

       V1. The "closed" and "curr" fields are correct:

           f.closed == closed(f)
           f.curr == curr(f)

       V2. The current position is either contained in the buffer,
           or just past the buffer:

           f.lo <= f.curr <= f.hi

       V3. Any (possibly) unflushed characters are stored
           in "f.buff":

           (forall i in [f.lo, f.curr):
             c(f)[i] == f.buff[i - f.lo])

       V4. For all characters not covered by V3, c(f) and
           disk(f) agree:

           (forall i in [f.lo, len(f)):
             i not in [f.lo, f.curr) => c(f)[i] == disk(f)[i])

       V5. "f.dirty" is true iff the buffer contains bytes that
           should be flushed to the file; by V3 and V4, only part
           of the buffer can be dirty.

           f.dirty ==
           (exists i in [f.lo, f.curr):
             c(f)[i] != f.buff[i - f.lo])

       V6. this.maxHi == this.lo + this.buff.length
       
       Note that "f.buff" can be "null" in a valid file, since the
       range of characters in V3 is empty when "f.lo == f.curr".
       
       A file is said to be *ready* if the buffer contains the
       current position, i.e., when:
       
       R1. !f.closed && f.buff != null
           && f.lo <= f.curr && f.curr < f.hi
           
       When a file is ready, reading or writing a single byte
       can be performed by reading or writing the in-memory
       buffer without performing a disk operation.
    */

    /** Open a new <code>BufferedRandomAccessFile</code> on
        <code>file</code> in mode <code>mode</code>, which
        should be "r" for reading only, or "rw" for reading
        and writing. */
    public BufferedRandomAccessFile(File file, String mode)
    throws IOException {
      super(file, mode);
      this.init();
    }

    /** 
     * Open a new <code>BufferedRandomAccessFile</code> on the
     * file named <code>name</code> in mode <code>mode</code>, 
     * which should be "r" for reading only, or "rw" for reading
     * and writing.
     */
    public BufferedRandomAccessFile(String name, String mode)
    throws IOException 
    {
        // Simon Z. replaced the original:
        //    super(name, mode);
        //    this.init();
        // with this.
        this(new File (name), mode);
    }
    
    /* Initialize the private fields of the file so as to
       make it valid. */
    private void init() {
      this.dirty = false;
      // SZ Feb 24, 2009: never read locally
      // this.closed = false;
      this.lo = this.curr = this.hi = 0;
      synchronized (mu) {
	this.buff =
	  (numAvailBuffs > 0) ? availBuffs[--numAvailBuffs] : new byte[BuffSz];
      }
      this.maxHi = BuffSz;
      this.hitEOF = false;
      this.diskPos = 0L;
    }
    
    /* overrides RandomAccessFile.close() */
    public void close() throws IOException {
        // Assert.check(!this.closed);
        this.flush();
        // SZ Feb 24, 2009: never read locally
        // this.closed = true;
        synchronized (mu) {
            // grow "availBuffs" array if necessary
            if (numAvailBuffs >= availBuffs.length) {
                byte[][] newBuffs = new byte[numAvailBuffs + 10][];
                System.arraycopy(availBuffs, 0, newBuffs, 0, numAvailBuffs);
                availBuffs = newBuffs;
            }
            availBuffs[numAvailBuffs++] = this.buff;
        }
        super.close();
    }
    
    /** Flush any bytes in the file's buffer that have not
        yet been written to disk. If the file was created
        read-only, this method is a no-op. */
    public void flush() throws IOException {
        // Assert.check(!this.closed);
        this.flushBuffer();
    }
    
    /* Flush any dirty bytes in the buffer to disk. */
    private void flushBuffer() throws IOException {
        if (this.dirty) {
            // Assert.check(this.curr > this.lo);
            if (this.diskPos != this.lo) super.seek(this.lo);
            int len = (int)(this.curr - this.lo);
            super.write(this.buff, 0, len); 
            this.diskPos = this.curr;
            this.dirty = false;
        }
    }
    
    /* Read at most "this.buff.length" bytes into "this.buff",
       returning the number of bytes read. If the return result
       is less than "this.buff.length", then EOF was read. */
    private int fillBuffer() throws IOException {
        int cnt = 0;
        int rem = this.buff.length;
        while (rem > 0) {
            int n = super.read(this.buff, cnt, rem); 
            if (n < 0) break;
            cnt += n;
            rem -= n;
        }
        this.hitEOF = (cnt < this.buff.length);
        this.diskPos += cnt;
        return cnt;
    }

    /* overrides RandomAccessFile.seek(long) */
    public void seek(long pos) throws IOException {
        // Assert.check(!this.closed);
        if (pos >= this.hi || pos < this.lo) {
            // seeking outside of current buffer -- flush and read
            this.flushBuffer();
            this.lo = pos & BuffMask; // start at BuffSz boundary
            this.maxHi = this.lo + this.buff.length;
            if (this.diskPos != this.lo) {
                super.seek(this.lo); 
                this.diskPos = this.lo;
            }
            int n = this.fillBuffer();
            this.hi = this.lo + n;
        }
	else {
            // seeking inside current buffer -- no read required
            if (pos < this.curr) {
                // if seeking backwards, we must flush to maintain V4
                this.flushBuffer();
            }
        }
        this.curr = pos;
    }
    
    /* extends this.seek(long) by return if a page has been read (used for statistics) */
    //TODO come up with better name for seeek %)
    public boolean seeek(long pos) throws IOException {
		boolean pageReadNeeded = true;
		// Assert.check(!this.closed);
		if (pos >= this.hi || pos < this.lo) {
			// seeking outside of current buffer -- flush and read
			this.flushBuffer();
			this.lo = pos & BuffMask; // start at BuffSz boundary
			this.maxHi = this.lo + this.buff.length;
			if (this.diskPos != this.lo) {
				super.seek(this.lo);
				this.diskPos = this.lo;
			}
			int n = this.fillBuffer();
			this.hi = this.lo + n;
		} else {
			// seeking inside current buffer -- no read required
			if (pos < this.curr) {
				// if seeking backwards, we must flush to maintain V4
				this.flushBuffer();
			} else {
				pageReadNeeded = false;
			}
		}
		this.curr = pos;
		return pageReadNeeded;
	}

    /* overrides RandomAccessFile.getFilePointer() */
    public long getFilePointer() {
        // Assert.check(!this.closed);
        return this.curr;
    }
    
    /* overrides RandomAccessFile.length() */
    public long length() throws IOException {
        // Assert.check(!this.closed);
        return Math.max(this.curr, super.length());
    }
    
    /* overrides RandomAccessFile.read() */
    public int read() throws IOException {
        // Assert.check(!this.closed);
        if (this.curr == this.hi) {
            // test for EOF
            // if (this.hi < this.maxHi) return -1;
            if (this.hitEOF) return -1;
                
            // slow path -- read another buffer
            this.seek(this.curr);
            if (this.curr == this.hi) return -1;
        }
        // Assert.check(this.curr < this.hi);
        byte res = this.buff[(int)(this.curr - this.lo)];
        this.curr++;
        return ((int)res) & 0xFF; // convert byte -> int
    }
    
    /* overrides RandomAccessFile.read(byte[]) */
    public int read(byte[] b) throws IOException {
        return this.read(b, 0, b.length);
    }
    
    /* overrides RandomAccessFile.read(byte[], int, int) */
    public int read(byte[] b, int off, int len) throws IOException {
        // Assert.check(!this.closed);
        if (this.curr == this.hi) {
            // test for EOF
            // if (this.hi < this.maxHi) return -1;
            if (this.hitEOF) return -1;
                
            // slow path -- read another buffer
            this.seek(this.curr);
            if (this.curr == this.hi) return -1;
        }
        // Assert.check(this.curr < this.hi);
        len = Math.min(len, (int)(this.hi - this.curr));
        int buffOff = (int)(this.curr - this.lo);
        System.arraycopy(this.buff, buffOff, b, off, len);
        this.curr += len;        
        return len;
    }

    public BigInteger readBigInteger(int size) throws IOException {
      byte[] b = new byte[size];
      // Assert.check(this.read(b) == size);
      return new BigInteger(b);
    }

  public final int readNat() throws IOException {
    int res = this.readShort();
    if (res >= 0) return res;
    res = (res << 16) | (this.readShort() & 0xffff);
    return -res;
  }

  public final long readLongNat() throws IOException {
    long res = this.readInt();
    if (res >= 0) return res;
    res = (res << 32) | ((long)this.readInt() & 0xffffffffL);
    return -res;
  }

    /* overrides RandomAccessFile.write(int) */
    public void write(int b) throws IOException {
        // Assert.check(!this.closed);
        if (this.curr == this.hi) {
            if (this.hitEOF && this.hi < this.maxHi) {
                // at EOF -- bump "hi"
                this.hi++;
            }
	    else {
                // slow path -- write current buffer; read next one
                this.seek(this.curr);
                if (this.curr == this.hi) {
                    // appending to EOF -- bump "hi"
                    // Assert.check(this.hitEOF);
                    this.hi++;
                }
            }
        }
        // Assert.check(this.curr < this.hi);
        this.buff[(int)(this.curr - this.lo)] = (byte)b;
        this.curr++;
        this.dirty = true;
    }
    
    /* overrides RandomAccessFile.write(byte[]) */
    public void write(byte[] b) throws IOException {
        this.write(b, 0, b.length);
    }
    
    /* overrides RandomAccessFile.write(byte[], int, int) */
    public void write(byte[] b, int off, int len) throws IOException {
        // Assert.check(!this.closed);
        while (len > 0) {
            int n = this.writeAtMost(b, off, len);
            off += n;
            len -= n;
        }
        this.dirty = true;
    }

    public void writeBigInteger(BigInteger bi, int size) throws IOException {
      byte[] b = bi.toByteArray();
      // Assert.check(b.length <= size);
      this.write(b, 0, size);
    }

  /* Precondition: x is a non-negative int. */
  public final void writeNat(int x) throws IOException {
    if (x <= 0x7fff) {
      this.writeShort((short)x);
    }
    else {
      this.writeInt(-x);
    }
  }

  /* Precondition: x is a non-negative long. */
  public final void writeLongNat(long x) throws IOException {
    if (x <= 0x7fffffff) {
      this.writeInt((int)x);
    }
    else {
      this.writeLong(-x);
    }
  }

    /* Write at most "len" bytes to "b" starting at position "off",
       and return the number of bytes written. */
    private int writeAtMost(byte[] b, int off, int len)
      throws IOException {
        if (this.curr == this.hi) {
            if (this.hitEOF && this.hi < this.maxHi) {
                // at EOF -- bump "hi"
                this.hi = this.maxHi;
            } else {
                // slow path -- write current buffer; read next one
                this.seek(this.curr);
                if (this.curr == this.hi) {
                    // appending to EOF -- bump "hi"
                    // Assert.check(this.hitEOF);
                    this.hi = this.maxHi;
                }
            }
        }
        // Assert.check(this.curr < this.hi);
        len = Math.min(len, (int)(this.hi - this.curr));
        int buffOff = (int)(this.curr - this.lo);
        System.arraycopy(b, off, this.buff, buffOff, len);
        this.curr += len;
        return len;
    }

  public static void main(String[] args) throws IOException {
    String name = "xxx";
    String mode = "rw";
    BufferedRandomAccessFile braf = new BufferedRandomAccessFile(name, mode);
    int x = 100;
    braf.writeLong(x); braf.writeLong(x); braf.writeLong(x);
    System.err.println("len = " + braf.length() + ", pos = " + braf.getFilePointer());
    braf.close();
    braf = new BufferedRandomAccessFile(name, mode);
    System.err.println("len = " + braf.length() + ", pos = " + braf.getFilePointer());
    braf.seek(braf.length());
    System.err.println("len = " + braf.length() + ", pos = " + braf.getFilePointer());
    braf.writeLong(x); braf.writeLong(x); braf.writeLong(x);
    System.err.println("len = " + braf.length() + ", pos = " + braf.getFilePointer());
  }
  
}
