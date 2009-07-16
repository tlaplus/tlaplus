// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
/*  Notes: If imporved efficiency is needed, one place to look is at
    int to byte arrays and BigInts to byte arrays and back,
    because I use the built in Java routines, and it may be possible
    to optimize them. 
 */
package tlc2.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Vector;


// SZ Feb 20, 2009: tests moved to the unit-test source folder, imports organized 
public class ByteUtils {


  /*
   * Input: No restrictions.  Output: a byte array of size 4 (this
   * is all that's needed for a Java integer) that when converted to
   * a BigInt equals the BigInt corresponding to x.
   */
  public static byte[] intToByteArray(int x) {
    byte[] b = new byte[4];
    b[0] = (byte) (x >>> 24);
    b[1] = (byte) (x >>> 16);
    b[2] = (byte) (x >>>  8);
    b[3] = (byte) (x       );
    return b;
  }

  /*
   * Input: No restrictions.  Output: a byte array of size 8 (this
   * is all that's needed for a Java long) that when converted to
   * a BigInt equals the BigInt corresponding to x.
   */
  public static byte[] longToByteArray(long x) {
    byte[] b = new byte[8];
    b[0] = (byte) (x >>> 56);
    b[1] = (byte) (x >>> 48);
    b[2] = (byte) (x >>> 40);
    b[3] = (byte) (x >>> 32);
    b[4] = (byte) (x >>> 24);
    b[5] = (byte) (x >>> 16);
    b[6] = (byte) (x >>>  8);
    b[7] = (byte) (x       );
    return b;
  }

  /*
   * Output: Converts the BigInt corresponding to bA to an int
   * and returns it. Standard narrowing primitive conversion as per
   * The Java Language Specification.
   */
  public static int byteArrayToInt(byte[] b) {
    int i0 = (b[0] & 0xFF) << 24;
    int i1 = (b[1] & 0xFF) << 16;
    int i2 = (b[2] & 0xFF) << 8;
    int i3 = (b[3] & 0xFF);
    return (i0 | i1 | i2 | i3);
  }

  /*
   * Output: Converts the BigInt corresponding to bA to a long
   * and returns it. Standard narrowing primitive conversion as per
   * The Java Language Specification.
   */
  public static long byteArrayToLong(byte[] b) {
    long i0 = (b[0] & 0xFF) << 56;
    long i1 = (b[1] & 0xFF) << 48;
    long i2 = (b[2] & 0xFF) << 40;
    long i3 = (b[3] & 0xFF) << 32;
    long i4 = (b[4] & 0xFF) << 24;
    long i5 = (b[5] & 0xFF) << 16;
    long i6 = (b[6] & 0xFF) << 8;
    long i7 = (b[7] & 0xFF);
    return (i0 | i1 | i2 | i3 | i4 | i5 | i6 | i7);
  }

  /*
   * Input: length must be >= the number of bytes required to store
   * b.  Output: a byte array of size length that when converted to a
   * BigInt equals b.  If b requires a byte array of size greater
   * than length, a runtime error is thrown.
   */
  public static byte[] bigIntToByteArray(BigInt b, int len) throws IOException{
    byte[] bA = b.toByteArray();
    return byteArrayToByteArray(bA, len);
  }

  /*
   * Input: length must be >= the length of bA.  Output: a byte array
   * of size length that when converted to a BigInt equals bA
   * If the length of bA > length, a runtime error is thrown.
   */
  public static byte[] byteArrayToByteArray(byte[] bA, int length) throws IOException{
    if (bA.length > length) {
        throw new IOException("byteArrayToByteArray: b needs more than length bytes.");
    }
    
    int bi, li;  // counters for bA, lA
    byte[] lA = new byte[length];
    
    // The byte array corresponding to a BigInt is big endian,
    // i.e. the zeroth byte is the most significant, therefore, we pad
    // lA with zeros (if non-negative) or ones (if negative) starting
    // from the beginning of the array, and copy bA from the end.
    li = length-1;
    for (bi = bA.length-1; bi >= 0; bi--) {
      lA[li--] = bA[bi];
    }
    
    if (bA[0] < 0)
      for (; li >= 0; li--) lA[li] = -1;
    else
      for (; li >= 0; li--) lA[li] = 0;
    
    return lA;
  }

  /* *************************************************************************** 
     Utility functions for writing to OutputStreams
     ***************************************************************************  */

  /*
   * Converts i to a byte array and writes the result to out.
   * @see intToByteArray
   */
  public static void writeInt(OutputStream out, int i)
  throws IOException {
    out.write(intToByteArray(i));
  }

  /*
   * Converts l to a byte array and writes the result to out.
   * @see longToByteArray
   */
  public static void writeLong(OutputStream out, long l)
  throws IOException {
    out.write(longToByteArray(l));
  }

  /*
   * Writes the size of bA (using four bytes) and bA to out. The size
   * of bA should be expressible as an integer.
   */
  public static void writeSizeByteArray(OutputStream out, byte[] bA)
  throws IOException {
    int len = bA.length;
    writeInt(out, len);
    out.write(bA);
  }

  /* Converts b to a byte array and calls writeSizeByteArray. */
  public static void writeSizeBigInt(OutputStream out, BigInt b)
  throws IOException {
    writeSizeByteArray(out, b.toByteArray());
  }

  /*
   * Writes bA to out, using length bytes.  Input: the length of bA
   * should be <= length, otherwise, a runtime error is thrown.
   */
  public static void writeByteArray(OutputStream out, byte[] bA, int len)
  throws IOException {
    int bAlen = bA.length;

    if (bAlen > len) {
        throw new IOException("writeByteArray: the byte array too large");
    }
    out.write(byteArrayToByteArray(bA, len));
  }

  /* Converts b to a byte array and calls writeByteArray. */
  public static void writeBigInt(OutputStream out, BigInt b, int len)
  throws IOException {
    
    writeByteArray(out, b.toByteArray(), len);
  }

  /*
   * Writes the length of the sub array and then (length, byte[])
   * pairs (for each BigInt in the sub array) to out.  The
   * subarray starts at A[start] and finishes at A[finish].  byte[]
   * is the byte array representation of the BigInt, and length
   * is the size of byte[]
   */
  public static void writeSizeArrayOfSizeBigInts 
  (BigInt[] A, int start, int finish, OutputStream out) 
  throws IOException {
    writeInt(out, finish-start+1);
    writeArrayOfSizeBigInts(A,start,finish,out);
  }
  
  /*
   * Writes (length, byte[]) pairs (for each BigInt in the sub
   * array) to out.  The subarray starts at A[start] and finishes at
   * A[finish].  byte[] is the byte array representation of the
   * BigInt, and length is the size of byte[].
   */
  public static void writeArrayOfSizeBigInts
  (BigInt[] A, int start, int finish, OutputStream out) 
  throws IOException {
    for (int i = start; i <= finish; i++) 
      writeSizeByteArray(out, A[i].toByteArray());
  }

  /* *************************************************************************** 
     Utility functions for reading InputStreams
     ***************************************************************************  */

  /** Reads len bytes from in and places in b starting at off and
      returns len.  Input: in should have at least len bytes; if not,
      then -1 is returned if no bytes are available (end of stream) or
      all of the remaining bytes are placed in b, starting at off and
      this number is returned.  Output: The number of bytes read is
      returned or -1 is the stream is empty.  This should be used
      instead of the read provided by any of the InputStreams; this is
      because for such streams (e.g. BufferedInputStream and
      GZIPOutputStream) if you use the given read routines to read in
      x bytes, but the buffer has some, but not enough bytes, then you
      don't get them all; you just get what the buffer has. This
      version fixes that problem. */
  public static int read(InputStream in, byte[] b, int off, int len) 
  throws IOException { 
    int cnt = 0;
    while (cnt < len) {
      int readOnce = in.read(b, off+cnt, len-cnt);
      if (readOnce <= 0) break;
      cnt += readOnce;
    }
    return cnt;
  }
  
  public static int read(InputStream in, byte[] b) 
  throws IOException {
    return read(in, b, 0, b.length);
  }
  
  /*
   * Reads an integer from in.  Input: there must at least four bytes
   * in in, otherwise if there are no bytes, an IOException is thrown
   * (to be used as an end of stream test), but if there are not
   * enough bytes, a runtime error is thrown.  Output: The integer
   * corresponding to the next four bytes.  
   */
  public static int readInt(InputStream in) throws IOException {
    byte[] b = new byte[4];
    int cnt = read(in, b);

    if (cnt < 4) {
      if (cnt <= 0) {
          throw new IOException("readInt: the input stream is empty.");
      }
      else {
          throw new IOException("readInt: not enought bytes.");
      }
    }
    return byteArrayToInt(b);
  }

  /** Reads a long from in.  Input: there must at least eight bytes
      in in, otherwise if there are no bytes, an IOException is thrown
      (to be used as an end of stream test), but if there are not
      enough bytes, a runtime error is thrown.  Output: The long
      corresponding to the next eight bytes.  
      @see byteArrayToLong */
  public static long readLong(InputStream in) throws IOException {
    byte b[] = new byte[8];
    int cnt = read(in, b);

    if (cnt < 8) {
      if (cnt <= 0) {
          throw new IOException("readLong: the imput stream is empty.");
      }
      else {
          throw new IOException("readLong: not enought bytes.");
      }
    }
    return byteArrayToLong(b);
  }

  /*
   * Reads an integer (len) and then a byte array of length len and
   * returns it.  Input: there must at least four bytes in in (for
   * len) and then len bytes, otherwise if in is empty, an
   * IOException is thrown, but if there are not enough bytes, a
   * RuntimeException is thrown.
   */
  public static byte[] readSizeByteArray(InputStream in) throws IOException {
    int len = readInt(in);
    byte[] bA = new byte[len];    
    int cnt = read(in, bA);

    if (cnt != len) {
        throw new IOException("readSizeByteArray: not enough bytes.");
    }
    return bA;
  }

  /*
   * Reads an integer (len) and then a BigInt (as a byte array of
   * length len) and returns it.  Input: there must at least four
   * bytes in in (for len) and then len bytes, otherwise if in is
   * empty, an IOException is thrown, but if there are not enough
   * bytes, a RuntimeException is thrown.
   */
  public static BigInt readSizeBigInt(InputStream in) 
  throws IOException {
    int len = readInt(in);
    byte[] bA = new byte[len];    
    int cnt = read(in, bA);

    if (cnt != len) {
        throw new IOException("readSizeBigInt: not enough bytes.");
    }
    return new BigInt(bA);
  }

  /*
   * Reads an integer (len) and then a len (size byte[]) pairs and
   * returns an array of BigInts corresponding to the byte[]s.
   * If the stream is empty when reading len, an IOException is
   * thrown; if at any other time, an IO error occurs, a
   * RuntimeException is thrown.  size is the size of the byte[]
   * read.  Input: there must at least len (size byte[]) pairs, where
   * len, size are four bytes.
   */
  public static BigInt[] readSizeArrayOfSizeBigInts(InputStream in) 
  throws IOException  {
    int len;
    BigInt[] A;

    try {
      len = readInt(in);
    }
    catch (IOException e) {
      throw new IOException("Can't read an array of BigInts from the input stream; it's empty.");
    }
    
    A = new BigInt[len];

    try {
    for (int i = 0; i<len; i++)
      A[i] = readSizeBigInt(in);
    }
    catch (IOException e) 
    {
        throw new IOException("Can't read an array of BigInts from the input stream; not enough bytes, but not empty.");
    }
    return A;
  }

  /** Reads in as many (size byte[]) pairs as it can and returns an
      array of BigInts corresponding to the byte[]s.  Input: in
      should contain some sequence of (size byte[]) pairs that are
      consistent, i.e. there really are size bytes in the stream,
      otherwise a RuntimeException is thrown */
  public static BigInt[] readArrayOfSizeBigInts(InputStream in) 
  throws IOException{
  
    Vector A = new Vector();
    int i = 0;

    try {
      do {
	A.addElement(readSizeBigInt(in));
	i++;
      } while (true);
    }
    catch (IOException e) {}
    
    BigInt[] bA = new BigInt[i];
    
    for (int j=0; j<i; j++)
      bA[j] = (BigInt) A.elementAt(j);
    
    return bA;
  }
  
  /*
   * Reads an integer from in, and appends that many bytes arrays to
   * out.  Input: If in is empty, an IOException is thrown; if it
   * doesn't have enough bytes, a RuntimeException is throw.
   */
  public static void appendByteArray(InputStream in, OutputStream out)
  throws  IOException {
    int i;
    
    try {
      i = readInt(in);
    }
    catch (IOException e) {
      throw new IOException("Can't append in to out; in is empty.");
    }
    try {
      for (int j = 0; j < i; j++)
	writeSizeByteArray(out, readSizeByteArray(in));
    }
    catch (IOException e) {
        throw new IOException("Can't append in to out; not enough bytes, but not empty.");
    }
  }

  /*
   * Reads an integer from in, and appends that integer and that many
   * bytes arrays to out.  Input: If in is empty, an IOException is thrown;
   * if it doesn't have enough bytes, a RuntimeException is throw.
   */
  public static void appendSizeByteArray(InputStream in, OutputStream out)
  throws  IOException {
    int i;
    
    try {
      i = readInt(in);
    }
    catch (IOException e) {
      throw new IOException("Can't append in to out; in is empty.");
    }
    writeInt(out,i);
    try {
      for (int j=0; j<i; j++)
	writeSizeByteArray(out, readSizeByteArray(in));
    }
    catch (IOException e) {
        throw new IOException("Can't append in to out; not enough bytes, but not empty.");
    }
  }

  
  /* *************************************************************************** 
     Pretty printing code.
     ***************************************************************************  */
  public static String printHex(byte[] b) {
    StringBuffer res = new StringBuffer();
    StringBuffer t, t1;

    for (int i = 0; i < b.length; i++) {
      t = new StringBuffer(Integer.toHexString(b[i]));
      if (t.length() > 2) {
	t1 = new StringBuffer();
	t1.append(t.charAt(t.length()-2));
	t1.append(t.charAt(t.length()-1));
	t = t1;
      } 
      res.append(t);
    }	
    return res.toString();
  }



}
