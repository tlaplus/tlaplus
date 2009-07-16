// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
/*  Notes: If imporved efficiency is needed, one place to look is at
    int to byte arrays and BigIntegers to byte arrays and back,
    because I use the built in Java routines, and it may be possible
    to optimize them. 
 */
package tlc2.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Vector;

public class ExSortUtils
{

    /** Writes the length of the sub array and then each element of A in
        the appropriate range to out.  The subarray starts at A[start]
        and finishes at A[finish].  */
    public static void writeSizeArrayOfExternalSortable(ExternalSortable[] A, int start, int finish, OutputStream out)
            throws IOException
    {
        ByteUtils.writeInt(out, finish - start + 1);
        writeArrayOfExternalSortable(A, start, finish, out);
    }

    /** Writes each element of A in the appropriate range to out.  The
        subarray starts at A[start] and finishes at A[finish].  */
    public static void writeArrayOfExternalSortable(ExternalSortable[] A, int start, int finish, OutputStream out)
            throws IOException
    {
        for (int i = start; i <= finish; i++)
            A[i].write(out);
    }

    /** Reads an integer (len) and then len ExternalSortables and
        returns an array corresponding to the ExternalSortables.
        If the stream is empty when reading len, an IOException is
        thrown; if at any other time, an IO error occurs, a
        RuntimeException is thrown. */
    public static ExternalSortable[] readSizeArrayOfExternalSortable(InputStream in, ExternalSortable ex)
            throws IOException
    {
        int len;

        try
        {
            len = ByteUtils.readInt(in);
        } catch (IOException e)
        {
            throw new IOException("Can't read an array of ExternalSortables from the input stream; it's empty.");
        }

        ExternalSortable[] A = new ExternalSortable[len];

        try
        {
            for (int i = 0; i < len; i++)
            {
                A[i] = ex.read(in);
            }
        } catch (IOException e)
        {
            throw new IOException(
                    "Can't read an array of ExternalSortables from the input stream; not enough bytes, but not empty.");
        }
        return A;
    }

    /** Reads in as many ExternalSortables as it can and returns an
        array corresponding to the ExternalSortables.  Input: in should
        contain some sequence of ExternalSortables, otherwise a
        RuntimeException is thrown */
    public static ExternalSortable[] readArrayOfExternalSortable(InputStream in, ExternalSortable ex)
            throws IOException
    {

        Vector A = new Vector();
        int i = 0;

        try
        {
            do
            {
                A.addElement(ex.read(in));
                i++;
            } while (true);
        } catch (IOException e)
        {
        }

        ExternalSortable[] eA = new ExternalSortable[i];

        for (int j = 0; j < i; j++)
            eA[j] = (ExternalSortable) A.elementAt(j);

        return eA;
    }

    /** Reads an integer from in, and appends that integer and that many
        objects to out.  Input: If in is empty, an IOException is thrown;
        if it doesn't have enough bytes, a RuntimeException is throw. */
    public static void appendSizeExternalSortableArraySizeArray(InputStream in, OutputStream out, ExternalSortable ex)
            throws IOException
    {
        int i;
        ExternalSortable a;

        try
        {
            i = ByteUtils.readInt(in);
        } catch (IOException e)
        {
            throw new IOException("Can't append in to out; in is empty.");
        }
        ByteUtils.writeInt(out, i);
        try
        {
            for (int j = 0; j < i; j++)
            {
                a = ex.read(in);
                a.write(out);
            }
        } catch (IOException e)
        {
            throw new IOException("Can't append in to out; not enough bytes, but not empty.");
        }
    }

    /** Reads an integer from in, and appends that many objects to out.
        Input: If in is empty, an IOException is thrown; if it doesn't
        have enough bytes, a RuntimeException is throw. */
    public static void appendSizeExternalSortableArrayArray(InputStream in, OutputStream out, ExternalSortable ex)
            throws IOException
    {
        int i;
        ExternalSortable a;

        try
        {
            i = ByteUtils.readInt(in);
        } catch (IOException e)
        {
            throw new IOException("Can't append in to out; in is empty.");
        }
        try
        {
            for (int j = 0; j < i; j++)
            {
                a = ex.read(in);
                a.write(out);
            }
        } catch (IOException e)
        {
            throw new IOException("Can't append in to out; not enough bytes, but not empty.");
        }
    }
}
