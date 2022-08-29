package tlc2.util;

import org.junit.Before;
import org.junit.Test;
import util.ToolIO;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.Random;

/**
 * Test case for BinUtils
 *
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ByteUtilsTest {
    public static final int ARRAYSIZE = 10000;
    public static final int BITS = 1000;
    long t1;
    long t2;
    private File testFileA;

    @Before
    public void setUp() throws Exception {
        // create temp files for unit tests
        testFileA = File.createTempFile("ByteUtilsTestA", null);
        testFileA.deleteOnExit();

        File testFileB = File.createTempFile("ByteUtilsTestB", null);
        testFileB.deleteOnExit();

        // SZ Feb 20, 2009: no ide what it is for...
        // to load classes ?
        // Class args[] = { Class.forName("java.math.BigInt"), Class.forName("java.math.BigInt") };

    }

    @Test
    public void test1() {
        t1 = System.currentTimeMillis();
        mainTestinttoByte();
        t2 = System.currentTimeMillis();
        ToolIO.out.println("Testing IntToByteArray took " + (t2 - t1) + "ms");
    }

    @Test
    public void test2() throws IOException {
        t1 = System.currentTimeMillis();
        mainTestWriteIntReadInt();
        t2 = System.currentTimeMillis();
        ToolIO.out.println("Testing WriteInt, ReadInt took " + (t2 - t1) + "ms");
    }


    private void mainTestinttoByte() {
        int i, j;
        byte[] b;
        final Random r = new Random();

        for (j = 0; j < 10000; j += 1) {
            i = r.nextInt();
            b = ByteUtils.intToByteArray(i);
            if ((i != ByteUtils.byteArrayToInt(b)) || (b.length != 4))
                ToolIO.out.println("i :" + i + "    byte :" + Arrays.toString(b) + "    i: " + ByteUtils.byteArrayToInt(b)
                        + "    size: " + b.length);
        }
    }

    private void mainTestWriteIntReadInt() throws IOException {
        final FileOutputStream fout = new FileOutputStream(testFileA);

        int i, j;
        final int[] A = new int[10000];

        final Random r = new Random();

        for (j = 0; j < 10000; j += 1) {
            A[j] = r.nextInt();
            ByteUtils.writeInt(fout, A[j]);
        }

        fout.flush();
        fout.close();

        final FileInputStream fin = new FileInputStream(testFileA);

        for (j = 0; j < 10000; j += 1) {
            i = ByteUtils.readInt(fin);
            if (i != A[j])
                ToolIO.out.println("i :" + i + "   A[j]: " + A[j]);
        }
    }


}
