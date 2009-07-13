// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Wed Oct 17 15:23:57 PDT 2001 by yuanyu
package util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/** A <code>BufferedDataOutputStream</code> is an optimized
    combination of a <code>java.io.BufferedOutputStream</code>
    and a <code>java.io.DataOutputStream</code>.<P>
   
    For efficiency, <code>BufferedDataOutputStream</code>s are 
    unmonitored. Hence, it is the client's responsibility to lock 
    the stream before using it. */

public class BufferedDataOutputStream extends FilterOutputStream {
    private byte[] buff; /* buffer of bytes to write */
    private int len;     /* number of valid bytes in "buff" */
    private byte[] temp; /* temporary array used by various methods */

    /* Object invariants:
       this.out == null <==> ``stream is closed''
       this.buff != null && 0 < this.buff.length
       0 <= this.len < this.buff.length
       this.temp != null && this.temp.length >= 8
    */

    /** Initialize this output stream. The stream will be closed
        initially; use the <code>open</code> method below to
        open it on an underlying <code>OutputStream</code>. */
    public BufferedDataOutputStream() {
        super(null);
        this.initFields();
    }

    /** Open this stream on the underlying output stream <code>os</code>. */
    public BufferedDataOutputStream(OutputStream os) {
        // Initialize fields
        super(os);
        this.initFields();
    }
    
    /** Open this output stream on the underlying output stream
        <code>new FileOutputStream(name)</code>. */
    public BufferedDataOutputStream(String name) throws IOException {
        this(new FileOutputStream(name));
    }
    
    /** Open this output stream on the underlying output stream
        <code>new FileOutputStream(file)</code>. */
    public BufferedDataOutputStream(File file) throws IOException {
        this(new FileOutputStream(file));
    }
    
    private void initFields() {
        this.buff = new byte[8192];
        this.len = 0;
        this.temp = new byte[8];
    }
    
    /** Reopen this output stream on <code>os</code>. This method need
        not be called on a newly initialized stream, but it can be called
        after the stream has been closed to re-open the stream on a
        different underlying stream without requiring internal resources
        to be re-allocated. */
    public void open(OutputStream os) throws IOException {
        this.out = os;
        this.len = 0;
    }
    
    /** Equivalent to <code>this.open(new FileOutputStream(name))</code>. */
    public void open(String name) throws IOException {
        this.open(new FileOutputStream(name));
    }

    /** Equivalent to <code>this.open(new FileOutputStream(file))</code>. */
    public void open(File file) throws IOException {
        this.open(new FileOutputStream(file));
    }

    /** Flush all bytes written to this stream to the underlying
        output stream. */
    public void flush() throws IOException {
        this.out.write(this.buff, 0, this.len);
        this.out.flush();
        this.len = 0;
    }

    /** Closes this stream and its underlying stream, after first
        flushing any buffered data. */
    public void close() throws IOException {
        this.flush();
        this.out.close();
        this.out = null;
    }
    
    /** Write <code>b</code> to this stream. */
    public void write(byte b) throws IOException {
        this.writeByte(b);
    }
    
    /** Write the <code>b.length</code> bytes of <code>b</code> to 
        this stream. */
    public void write(byte[] b) throws IOException {
        this.write(b, 0, b.length);
    }
    
    /** Write <code>n</code> bytes of <code>b</code> starting
        at possition <code>off</code> to this stream. */
    public void write(byte[] b, int off, int n) throws IOException {
        while (n > 0) {
            int toCopy = Math.min(n, this.buff.length - this.len);
            System.arraycopy(b, off, this.buff, this.len, toCopy);
            this.len += toCopy; off += toCopy; n -= toCopy;
            if (this.buff.length == this.len) {
                // write buffer to underlying stream
                this.out.write(this.buff, 0, this.len);
                this.len = 0;
            }
        }
    }
    
    /** Write the byte <code>b</code> to this stream. */
    public void writeByte(byte b) throws IOException {
        this.buff[this.len++] = b;
        if (this.buff.length == this.len) {
            // write buffer to underlying stream
            this.out.write(this.buff, 0, this.len);
            this.len = 0;
        }
    }
    
    /** Write the boolean value <code>b</code> to this stream as
        a single byte. */
    public void writeBoolean(boolean bool) throws IOException {
        byte b = (bool ? (byte)1 : (byte)0);
        this.writeByte(b);
    }
    
    /** Write the short value <code>s</code> to this stream as
        two bytes. */
    public void writeShort(short s) throws IOException {
        this.temp[0] = (byte) ((s >>> 8) & 0xff);
        this.temp[1] = (byte) (s & 0xff);
        this.write(this.temp, 0, 2);
    }
    
    /** Write the integer value <code>i</code> to this stream as
        four bytes. */
    public void writeInt(int i) throws IOException {
        this.temp[0] = (byte) ((i >>> 24) & 0xff);
        this.temp[1] = (byte) ((i >>> 16) & 0xff);
        this.temp[2] = (byte) ((i >>> 8) & 0xff);
        this.temp[3] = (byte) (i & 0xff);
        this.write(this.temp, 0, 4);
    }
    
    /** Write the long value <code>l</code> to this stream as
        eight bytes. */
    public void writeLong(long l) throws IOException {
        this.temp[0] = (byte) ((l >>> 56) & 0xff);
        this.temp[1] = (byte) ((l >>> 48) & 0xff);
        this.temp[2] = (byte) ((l >>> 40) & 0xff);
        this.temp[3] = (byte) ((l >>> 32) & 0xff);
        this.temp[4] = (byte) ((l >>> 24) & 0xff);
        this.temp[5] = (byte) ((l >>> 16) & 0xff);
        this.temp[6] = (byte) ((l >>> 8) & 0xff);
        this.temp[7] = (byte) (l & 0xff);
        this.write(this.temp, 0, 8);
    }
    
    /** Write the float value <code>f</code> to this stream as
        four bytes. */
    public void writeFloat(float f) throws IOException {
	    this.writeInt(Float.floatToIntBits(f));
    }
    
    /** Write the double value <code>d</code> to this stream as
        eight bytes. */
    public void writeDouble(double d) throws IOException {
	    this.writeLong(Double.doubleToLongBits(d));
    }

    /** Write the characters of the string <code>s</code> to this
        stream as a sequence of bytes. */
    public void writeString(String s) throws IOException {
        int n = s.length();
        int off = 0;
        while (n > 0) {
            int toCopy = Math.min(n, this.buff.length - this.len);
            s.getBytes(off, off + toCopy, this.buff, this.len);
            this.len += toCopy; off += toCopy; n -= toCopy;
            if (this.buff.length == this.len) {
                // write buffer to underlying stream
                this.out.write(this.buff, 0, this.len);
                this.len = 0;
            }
        }
    }
    
    /** Write <code>n</code> characters of <code>chars</code> starting 
        at offset <code>off</code> to this stream as a sequence of bytes. */
    public void writeChars(char[] chars, int off, int n) throws IOException {
        int finOff = off + n;
        while (off < finOff) {
            // Copy (part of) chars to this.buff
            int endOff = Math.min(finOff, off + this.buff.length - this.len);
            while (off < endOff) this.buff[this.len++] = (byte)chars[off++];

            // If this.buff is full, write it out
            if (this.buff.length == this.len) {
                // write buffer to underlying stream
                this.out.write(this.buff, 0, this.len);
                this.len = 0;
            }
        }        
    }
    
    /** Write the string <code>s</code> to the stream in such a way that it
        can be read back by <code>BufferedDataInputStream.readAnyString</code>,
        even if <code>s</code> is <code>null</code> or if it contains newline 
        characters. */
    public void writeAnyString(String s) throws IOException {
      if (s == null) {
	this.writeInt(-1);
      }
      else {
	this.writeInt(s.length());
	this.writeString(s);
      }
    }
    
    /** Write the characters of the string <code>s</code> to this
        stream as a sequence of bytes, followed by a newline. */
    public void writeLine(String s) throws IOException {
        this.writeString(s);
        this.writeByte((byte) '\n');
    }

}
