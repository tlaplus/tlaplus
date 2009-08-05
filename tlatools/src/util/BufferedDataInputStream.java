// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Wed Oct 17 15:23:57 PDT 2001 by yuanyu
package util;

import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FilterInputStream;
import java.io.IOException;
import java.io.InputStream;

import tlc2.output.EC;

/** A <code>BufferedDataInputStream</code> is an optimized
    combination of a <code>java.io.BufferedInputStream</code>
    and a <code>java.io.DataInputStream</code>. It also provides
    an <code>atEOF</code> method for detecting end-of-file.<P>
   
    For efficiency, <code>BufferedDataInputStream</code>s are
    unmonitored. Hence, it is the client's responsibility to lock 
    the stream before using it. This requirement is denoted in 
    the comments of this class by the specification 
    <TT>REQUIRES LL = SELF</TT>. */

public class BufferedDataInputStream extends FilterInputStream {
    /* protected by SELF */
    private byte[] buff;    /* buffer of bytes to read */
    private int len;        /* number of valid bytes in "buff" */
    private int curr;       /* position of next byte to return */
    private byte[] temp;    /* temporary array used by various methods */

    /* Object invariants:
       this.out == null <==> ``stream is closed''
       this.buff != null && 0 < this.buff.length
       this.len != 0
       this.len > 0 <==> 0 <= this.curr < this.len <= this.buff.length
       this.len < 0 <==> ``read EOF from underlying stream''
       this.temp != null && this.temp.length >= 8
    */

    /** Initialize this input stream. The stream will be closed
        initially; use the <code>open</code> method below to
        open it on an underlying <code>InputStream</code>. */
    public BufferedDataInputStream() {
        super(null);
        this.initFields();
    }

    /** Open this input stream on the underlying stream <code>is</code>. */
    public BufferedDataInputStream(InputStream is) throws IOException {
        super(is);
        this.initFields();
        this.len = this.in.read(this.buff);
        Assert.check(this.len != 0, EC.SYSTEM_STREAM_EMPTY);
    }
    
    /** Open this input stream on the underlying input stream
        <code>new FileInputStream(name)</code>. */
    public BufferedDataInputStream(String name) throws IOException {
        this(new FileInputStream(name));
    }
    
    /** Open this input stream on the underlying input stream
        <code>new FileOutputStream(file)</code>. */
    public BufferedDataInputStream(File file) throws IOException {
        this(new FileInputStream(file));
    }

    private void initFields() {
        this.buff = new byte[8192];
        this.curr = 0;
        this.temp = new byte[8];
    }
    
    /** REQUIRES LL = SELF */
    /** Re-open this input stream on <code>is</code>. This method need
        not be called on a newly initialized stream, but it can be called
        after the stream has been closed to re-open the stream on a
        different underlying stream without requiring internal resources
        to be re-allocated. */
    public void open(InputStream is) throws IOException {
        Assert.check(this.in == null, EC.SYSTEM_STREAM_EMPTY);
        this.in = is;
        this.len = this.in.read(this.buff);
        Assert.check(this.len != 0, EC.SYSTEM_STREAM_EMPTY);
    }
    
    /** Equivalent to <code>this.open(new FileInputStream(name))</code>. */
    public void open(String name) throws IOException {
        this.open(new FileInputStream(name));
    }

    /** REQUIRES LL = SELF */
    /** Closes this stream and its underlying stream. */
    public void close() throws IOException {
        this.in.close();
        this.in = null;
    }
    
    /** REQUIRES LL = SELF */
    /** Returns <code>true</code> iff the stream is exhausted. */
    public boolean atEOF() {
        return (this.len < 0);
    }
    
    /** REQUIRES LL = SELF */
    /** Reads up to <code>b.length</code> bytes into <code>b</code>, 
        and returns the number of bytes read, or -1 if the stream is 
        exhausted on entry. */
    public int read(byte[] b) throws IOException {
        return this.read(b, 0, b.length);
    }
    
    /** REQUIRES LL = SELF */
    /** Reads up to <code>n</code> bytes into <code>b</code> starting
        at position <code>off</code>, and returns the number of bytes
        read, or -1 if the stream is exhausted on entry. */
    public int read(byte[] b, int off, int n) throws IOException {
        if (this.len < 0) return -1;
        int offInit = off;
        while (n > 0 && this.len > 0) {
            int toCopy = Math.min(n, this.len - this.curr);
            System.arraycopy(this.buff, this.curr, b, off, toCopy);
            this.curr += toCopy; off += toCopy; n -= toCopy;
            if (this.curr == this.len) {
                // refill buffer from underlying input stream
                this.len = this.in.read(this.buff);
                Assert.check(this.len != 0, EC.SYSTEM_STREAM_EMPTY);
                this.curr = 0;
            }
        }
        return off - offInit;
    }
    
    /** REQUIRES LL = SELF */
    /** Reads <code>b.length</code> bytes into <code>b</code>, or
        throws <code>EOFException</code> if the stream contains fewer
        than <code>b.length</code> bytes. */
    public void readFully(byte[] b) throws IOException, EOFException {
        this.readFully(b, 0, b.length);
    }
    
    /** REQUIRES LL = SELF */
    /** Reads <code>n</code> bytes into <code>b</code> starting at
        position <code>off</code>, or throws <code>EOFException</code>
        if the stream contains fewer than <code>n</code> bytes. */
    public void readFully(byte[] b, int off, int n)
      throws IOException, EOFException {
        while (n > 0) {
            int numRead = this.read(b, off, n);
            if (numRead < 0) throw new EOFException();
            off += numRead; n -= numRead;
        }
    }
    
    /** REQUIRES LL = SELF */
    /** Reads and returns the next byte of this stream, or throws
        <code>EOFException</code> if the stream is exhausted. */
    public byte readByte() throws IOException, EOFException {
        if (this.len < 0) throw new EOFException();
        byte res = this.buff[this.curr++];
        if (this.curr == this.len) {
            // refill buffer from underlying input stream
            this.len = this.in.read(this.buff);
            Assert.check(this.len != 0, EC.SYSTEM_STREAM_EMPTY);
            this.curr = 0;
        }
        return res;
    }
    
    /** REQUIRES LL = SELF */
    /** Reads and returns the next <code>boolean</code> value
        encoded in the next byte of this stream, or
        throws <code>EOFException</code> if the stream is
        exhausted. */
    public boolean readBoolean() throws IOException, EOFException {
        return (this.readByte() != 0);
    }
    
    /** REQUIRES LL = SELF */
    /** Read and return the next <code>short</code> value
        encoded in the next two bytes of this stream, or
        throw <code>EOFException</code> if the stream contains
        fewer than two bytes. */
    public short readShort() throws IOException, EOFException {
        this.readFully(this.temp, 0, 2);
        return (short) ((temp[0] << 8) | (temp[1] & 0xff));
    }
        
    /** REQUIRES LL = SELF */
    /** Reads and returns the next <code>int</code> value
        encoded in the next four bytes of this stream, or
        throws <code>EOFException</code> if the stream contains
        fewer than four bytes. */
    public int readInt() throws IOException, EOFException {
        this.readFully(this.temp, 0, 4);
        int res = temp[0];
        res <<= 8; res |= (temp[1] & 0xff);
        res <<= 8; res |= (temp[2] & 0xff);
        res <<= 8; res |= (temp[3] & 0xff);
        return res;
    }
    
    /** REQUIRES LL = SELF */
    /** Reads and returns the next <code>long</code> value
        encoded in the next eight bytes of this stream, or
        throws <code>EOFException</code> if the stream contains
        fewer than eight bytes. */
    public long readLong() throws IOException, EOFException {
        this.readFully(this.temp, 0, 8);
        long res = temp[0];
        res <<= 8; res |= (temp[1] & 0xff);
        res <<= 8; res |= (temp[2] & 0xff);
        res <<= 8; res |= (temp[3] & 0xff);
        res <<= 8; res |= (temp[4] & 0xff);
        res <<= 8; res |= (temp[5] & 0xff);
        res <<= 8; res |= (temp[6] & 0xff);
        res <<= 8; res |= (temp[7] & 0xff);
        return res;
    }
    
    /** REQUIRES LL = SELF */
    /** Reads and returns the next line of text from this stream, or
        <code>null</code> if the stream is exhausted. Any end-of-line
        character(s) are not included in the result. A line is termined
        by a carriage return character (<code>'\r'</code>), a newline 
        character (<code>'\n'</code>), a carriage return immediately 
        followed by a newline, or by the end of the stream. */
    public String readLine() throws IOException {
        String res = null;
        while (this.len > 0) {
            for (int i = this.curr; i < this.len; i++) {
                if (this.buff[i] == (byte)'\n' || this.buff[i] == (byte)'\r') {
                    // remember EOL character
                    byte eol = this.buff[i];
                    
                    // create new substring
                    String s = new String(this.buff, /*offset=*/ this.curr,
					  /*count=*/ i - this.curr);
                    if (res == null) res = s; else res += s;
                    
                    // skip over bytes in stream
                    this.skip(i + 1 - this.curr);
                    
                    // skip '\n' if it follows '\r'
                    if (eol == (byte)'\r' && this.len > 0
                        && this.buff[this.curr] == (byte)'\n') {
                        this.readByte();
                    }
                    return res;
                }
            }
            // hit end of buffer -- append rest of buffer to "res"
            String s = new String(this.buff, /*offset=*/ this.curr,
				  /*count=*/ this.len - this.curr);
            if (res == null) res = s; else res += s;
            
            // skip over bytes in stream
            this.skip(this.len - this.curr);
        }
        // hit EOF without seeing EOL chars
        return res;
    }

    public String readString(int n) throws IOException {
      char[] b = new char[n];
      int off = 0;
      while (n > 0) {
	if (this.len < 0) throw new EOFException();
	int offInit = off;
	while (n > 0 && this.len > 0) {
	  int toCopy = Math.min(n, this.len - this.curr);
	  for (int i = 0; i < toCopy; i++) {
	    b[off+i] = (char)this.buff[this.curr+i];
	  }
	  this.curr += toCopy; off += toCopy; n -= toCopy;
	  if (this.curr == this.len) {
	    // refill buffer from underlying input stream
	    this.len = this.in.read(this.buff);
	    Assert.check(this.len != 0, EC.SYSTEM_STREAM_EMPTY);
	    this.curr = 0;
	  }
	}
	int numRead = off - offInit;
	off += numRead; n -= numRead;
      }
      return new String(b);
    }
  
    /** REQUIRES LL = SELF */
    /** Skips over the next <code>n</code> bytes in this stream,
        or throws <code>EOFException</code> if it contains fewer
        than <code>n</code> bytes. */
    public void skip(int n) throws IOException, EOFException {
        while (this.len > 0 && this.curr + n >= this.len) {
            n -= (this.len - this.curr);
            // refill buffer from underlying input stream
            this.len = this.in.read(this.buff);
            Assert.check(this.len != 0, EC.SYSTEM_STREAM_EMPTY);
            this.curr = 0;
        }
        if (n > 0 && this.len < 0) throw new EOFException();
        this.curr += n;
        Assert.check(this.len < 0 || this.curr < this.len, EC.SYSTEM_INDEX_ERROR);
    }

}
