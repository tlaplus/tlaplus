package tlc2.util;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.util.Random;

import junit.framework.TestCase;
import util.ToolIO;

/**
 * Test case for BinUtils
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ByteUtilsTest extends TestCase
{
    public static final int ARRAYSIZE = 10000;
    public static final int BITS = 1000;

    BigInteger Arr[];
    BigInteger Arr2[];
    BigInteger Arr3[];
    BigInteger Arr4[];
    BigInteger Arr5[];
    long t1;
    long t2;

    protected void setUp() throws Exception
    {
        super.setUp();
        Arr = new BigInteger[ARRAYSIZE];
        Arr2 = new BigInteger[ARRAYSIZE];
        Arr3 = new BigInteger[ARRAYSIZE];
        Arr4 = new BigInteger[ARRAYSIZE];
        Arr5 = new BigInteger[ARRAYSIZE];

        // SZ Feb 20, 2009: no ide what it is for...
        // to load classes ?
        // Class args[] = { Class.forName("java.math.BigInt"), Class.forName("java.math.BigInt") };

    }

    public void test1()
    {
        t1 = System.currentTimeMillis();
        mainTestinttoByte();
        t2 = System.currentTimeMillis();
        ToolIO.out.println("Testing IntToByteArray took " + (t2 - t1) + "ms");
    }

    public void test2() throws FileNotFoundException, IOException
    {
        t1 = System.currentTimeMillis();
        mainTestWriteIntReadInt();
        t2 = System.currentTimeMillis();
        ToolIO.out.println("Testing WriteInt, ReadInt took " + (t2 - t1) + "ms");
    }

    public void test3()
    {
        t1 = System.currentTimeMillis();
        mainTestlongtoByte();
        t2 = System.currentTimeMillis();
        ToolIO.out.println("Testing longToByteArray took " + (t2 - t1) + "ms");
    }

    public void test4() throws FileNotFoundException, IOException
    {
        t1 = System.currentTimeMillis();
        mainTestWriteLongReadLong();
        t2 = System.currentTimeMillis();
        ToolIO.out.println("Testing WriteLong, ReadLong took " + (t2 - t1) + "ms");
    }

    public void test5() throws FileNotFoundException, IOException
    {
        t1 = System.currentTimeMillis();
        mainTestWriteReadSizeByteArray();
        t2 = System.currentTimeMillis();
        ToolIO.out.println("Testing Write, Read took " + (t2 - t1) + "ms");
    }

    public void test6() throws FileNotFoundException, IOException
    {
        t1 = System.currentTimeMillis();
        mainTestAppend();
        t2 = System.currentTimeMillis();
        ToolIO.out.println("Testing Append took " + (t2 - t1) + "ms");
    }

    private void mainTestinttoByte()
    {
        int i, j;
        byte[] b;
        Random r = new Random();

        for (j = 0; j < 10000; j += 1)
        {
            i = r.nextInt();
            b = ByteUtils.intToByteArray(i);
            if ((i != ByteUtils.byteArrayToInt(b)) || (b.length != 4))
                ToolIO.out.println("i :" + i + "    byte :" + b + "    i: " + ByteUtils.byteArrayToInt(b)
                        + "    size: " + b.length);
        }
    }

    private void mainTestWriteIntReadInt() throws IOException, FileNotFoundException
    {
        FileOutputStream fout = new FileOutputStream("ByteUtilsTest.bin");

        int i, j;
        int A[] = new int[10000];

        Random r = new Random();

        for (j = 0; j < 10000; j += 1)
        {
            A[j] = r.nextInt();
            ByteUtils.writeInt(fout, A[j]);
        }

        fout.flush();
        fout.close();

        FileInputStream fin = new FileInputStream("ByteUtilsTest.bin");

        for (j = 0; j < 10000; j += 1)
        {
            i = ByteUtils.readInt(fin);
            if (i != A[j])
                ToolIO.out.println("i :" + i + "   A[j]: " + A[j]);
        }
    }

    private void mainTestlongtoByte()
    {
        long i, j;
        byte[] b;
        Random r = new Random();

        for (j = 0; j < 10000; j += 1)
        {
            i = r.nextLong();
            b = ByteUtils.longToByteArray(i);
            if ((i != ByteUtils.byteArrayToLong(b)) || (b.length != 8))
                ToolIO.out.println("i :" + i + "    byte :" + b + "    i: " + ByteUtils.byteArrayToLong(b)
                        + "    size: " + b.length);
        }
    }

    private void mainTestWriteLongReadLong() throws IOException, FileNotFoundException
    {
        FileOutputStream fout = new FileOutputStream("ByteUtilsTest.bin");

        long i;
        int j;
        long A[] = new long[10000];

        Random r = new Random();

        for (j = 0; j < 10000; j += 1)
        {
            A[j] = r.nextLong();
            ByteUtils.writeLong(fout, A[j]);
        }

        fout.close();

        FileInputStream fin = new FileInputStream("ByteUtilsTest.bin");

        for (j = 0; j < 10000; j += 1)
        {
            i = ByteUtils.readLong(fin);
            if (i != A[j])
                ToolIO.out.println("i :" + i + "   A[j]: " + A[j]);
        }
    }

    private void mainTestWriteReadSizeByteArray() throws IOException, FileNotFoundException
    {
        FileOutputStream fout = new FileOutputStream("ByteUtilsTest.bin");

        int j;
        BigInt[] A = new BigInt[ARRAYSIZE];
        BigInt[] B = new BigInt[ARRAYSIZE];
        BigInt[] C;

        mainInitialize(A, B);
        int half = (ARRAYSIZE - 1) / 2;

        ByteUtils.writeSizeArrayOfSizeBigInts(A, 0, half - 1, fout);
        ByteUtils.writeSizeArrayOfSizeBigInts(A, half, ARRAYSIZE - 1, fout);

        fout.flush();
        fout.close();

        FileInputStream fin = new FileInputStream("ByteUtilsTest.bin");

        B = ByteUtils.readSizeArrayOfSizeBigInts(fin);
        ByteUtils.readInt(fin);
        C = ByteUtils.readArrayOfSizeBigInts(fin);

        for (j = 0; j < half; j++)
        {
            if (!A[j].equals(B[j]))
                ToolIO.out.println("A[" + j + "] :" + A[j] + "   B[" + j + "]: " + B[j]);
        }

        for (j = half; j < ARRAYSIZE; j++)
        {
            if (!A[j].equals(C[j - half]))
                ToolIO.out.println("A[" + j + "] :" + A[j] + "   C[" + (j - half) + "]: " + C[j - half]);
        }
    }

    private void mainTestAppend() throws IOException, FileNotFoundException
    {
        FileOutputStream fout = new FileOutputStream("ByteUtilsTest.bin");

        int j;
        BigInt[] A = new BigInt[ARRAYSIZE];
        BigInt[] B = new BigInt[ARRAYSIZE];
        BigInt[] C;

        mainInitialize(A, B);
        int half = (ARRAYSIZE - 1) / 2;

        ByteUtils.writeSizeArrayOfSizeBigInts(A, 0, half - 1, fout);
        ByteUtils.writeSizeArrayOfSizeBigInts(A, half, ARRAYSIZE - 1, fout);

        fout.flush();
        fout.close();

        FileInputStream fin = new FileInputStream("ByteUtilsTest.bin");
        fout = new FileOutputStream("ByteUtilsTest2.bin");

        try
        {
            ByteUtils.appendSizeByteArray(fin, fout);
            ByteUtils.appendSizeByteArray(fin, fout);
            ByteUtils.appendSizeByteArray(fin, fout);
        } catch (IOException e)
        {
        }

        fin.close();
        fout.flush();
        fout.close();

        fin = new FileInputStream("ByteUtilsTest2.bin");

        B = ByteUtils.readSizeArrayOfSizeBigInts(fin);
        ByteUtils.readInt(fin);
        C = ByteUtils.readArrayOfSizeBigInts(fin);

        for (j = 0; j < half; j++)
        {
            if (!A[j].equals(B[j]))
                ToolIO.out.println("A[" + j + "] :" + A[j] + "   B[" + j + "]: " + B[j]);
        }

        for (j = half; j < ARRAYSIZE; j++)
        {
            if (!A[j].equals(C[j - half]))
                ToolIO.out.println("A[" + j + "] :" + A[j] + "   C[" + (j - half) + "]: " + C[j - half]);
        }
    }

    private void mainInitialize(BigInt[] Arr, BigInt[] Arr2)
    {
        Random r = new Random();

        for (int i = 0; i < ARRAYSIZE; i++)
        {
            Arr[i] = new BigInt(BITS, r);
            Arr2[i] = Arr[i];
        }
    }

}
