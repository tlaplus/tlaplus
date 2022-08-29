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


// SZ Feb 20, 2009: tests moved to the unit-test source folder, imports organized 
public class ByteUtils {


    /*
     * Input: No restrictions.  Output: a byte array of size 4 (this
     * is all that's needed for a Java integer) that when converted to
     * a BigInt equals the BigInt corresponding to x.
     */
    public static byte[] intToByteArray(final int x) {
        final byte[] b = new byte[4];
        b[0] = (byte) (x >>> 24);
        b[1] = (byte) (x >>> 16);
        b[2] = (byte) (x >>> 8);
        b[3] = (byte) (x);
        return b;
    }

    /*
     * Output: Converts the BigInt corresponding to bA to an int
     * and returns it. Standard narrowing primitive conversion as per
     * The Java Language Specification.
     */
    public static int byteArrayToInt(final byte[] b) {
        final int i0 = (b[0] & 0xFF) << 24;
        final int i1 = (b[1] & 0xFF) << 16;
        final int i2 = (b[2] & 0xFF) << 8;
        final int i3 = (b[3] & 0xFF);
        return (i0 | i1 | i2 | i3);
    }

    /*
     * Input: length must be >= the number of bytes required to store
     * b.  Output: a byte array of size length that when converted to a
     * BigInt equals b.  If b requires a byte array of size greater
     * than length, a runtime error is thrown.
     */
    public static byte[] bigIntToByteArray(final BigInt b, final int len) throws IOException {
        final byte[] bA = b.toByteArray();
        return byteArrayToByteArray(bA, len);
    }

    /*
     * Input: length must be >= the length of bA.  Output: a byte array
     * of size length that when converted to a BigInt equals bA
     * If the length of bA > length, a runtime error is thrown.
     */
    public static byte[] byteArrayToByteArray(final byte[] bA, final int length) throws IOException {
        if (bA.length > length) {
            throw new IOException("byteArrayToByteArray: b needs more than length bytes.");
        }

        int bi, li;  // counters for bA, lA
        final byte[] lA = new byte[length];

        // The byte array corresponding to a BigInt is big endian,
        // i.e. the zeroth byte is the most significant, therefore, we pad
        // lA with zeros (if non-negative) or ones (if negative) starting
        // from the beginning of the array, and copy bA from the end.
        li = length - 1;
        for (bi = bA.length - 1; bi >= 0; bi--) {
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
    public static void writeInt(final OutputStream out, final int i)
            throws IOException {
        out.write(intToByteArray(i));
    }


    /*
     * Writes the size of bA (using four bytes) and bA to out. The size
     * of bA should be expressible as an integer.
     */
    public static void writeSizeByteArray(final OutputStream out, final byte[] bA)
            throws IOException {
        final int len = bA.length;
        writeInt(out, len);
        out.write(bA);
    }

    /* Converts b to a byte array and calls writeSizeByteArray. */
    public static void writeSizeBigInt(final OutputStream out, final BigInt b)
            throws IOException {
        writeSizeByteArray(out, b.toByteArray());
    }



  /* *************************************************************************** 
     Utility functions for reading InputStreams
     ***************************************************************************  */

    /**
     * Reads len bytes from in and places in b starting at off and
     * returns len.  Input: in should have at least len bytes; if not,
     * then -1 is returned if no bytes are available (end of stream) or
     * all of the remaining bytes are placed in b, starting at off and
     * this number is returned.  Output: The number of bytes read is
     * returned or -1 is the stream is empty.  This should be used
     * instead of the read provided by any of the InputStreams; this is
     * because for such streams (e.g. BufferedInputStream and
     * GZIPOutputStream) if you use the given read routines to read in
     * x bytes, but the buffer has some, but not enough bytes, then you
     * don't get them all; you just get what the buffer has. This
     * version fixes that problem.
     */
    public static int read(final InputStream in, final byte[] b, final int off, final int len)
            throws IOException {
        int cnt = 0;
        while (cnt < len) {
            final int readOnce = in.read(b, off + cnt, len - cnt);
            if (readOnce <= 0) break;
            cnt += readOnce;
        }
        return cnt;
    }

    public static int read(final InputStream in, final byte[] b)
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
    public static int readInt(final InputStream in) throws IOException {
        final byte[] b = new byte[4];
        final int cnt = read(in, b);

        if (cnt < 4) {
            if (cnt <= 0) {
                throw new IOException("readInt: the input stream is empty.");
            } else {
                throw new IOException("readInt: not enought bytes.");
            }
        }
        return byteArrayToInt(b);
    }

    /*
     * Reads an integer (len) and then a BigInt (as a byte array of
     * length len) and returns it.  Input: there must at least four
     * bytes in in (for len) and then len bytes, otherwise if in is
     * empty, an IOException is thrown, but if there are not enough
     * bytes, a RuntimeException is thrown.
     */
    public static BigInt readSizeBigInt(final InputStream in)
            throws IOException {
        final int len = readInt(in);
        final byte[] bA = new byte[len];
        final int cnt = read(in, bA);

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
    public static BigInt[] readSizeArrayOfSizeBigInts(final InputStream in)
            throws IOException {
        final int len;
        final BigInt[] A;

        try {
            len = readInt(in);
        } catch (final IOException e) {
            throw new IOException("Can't read an array of BigInts from the input stream; it's empty.");
        }

        A = new BigInt[len];

        try {
            for (int i = 0; i < len; i++)
                A[i] = readSizeBigInt(in);
        } catch (final IOException e) {
            throw new IOException("Can't read an array of BigInts from the input stream; not enough bytes, but not empty.");
        }
        return A;
    }


}
