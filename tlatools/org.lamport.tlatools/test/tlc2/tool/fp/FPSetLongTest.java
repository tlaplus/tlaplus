package tlc2.tool.fp;

import org.junit.Test;
import org.junit.experimental.categories.Category;
import util.LongTest;

import java.util.Date;
import java.util.Random;

import static org.junit.Assert.*;

public abstract class FPSetLongTest extends AbstractFPSetTest {

    /**
     * Test filling a {@link FPSet} with four linearly incrementing values
     */
    @Category(LongTest.class)
    @Test
    public void testSimpleFill() throws Exception {
        final FPSet fpSet = getFPSet(new FPSetConfiguration());
        fpSet.init(1, tmpdir, filename);

        long fp = 1L;
        assertFalse(fpSet.put(fp));
        assertTrue(fpSet.contains(fp++));
        assertFalse(fpSet.put(fp));
        assertTrue(fpSet.contains(fp++));
        assertFalse(fpSet.put(fp));
        assertTrue(fpSet.contains(fp++));
        assertFalse(fpSet.put(fp));
        assertTrue(fpSet.contains(fp++));
    }

    /**
     * Test filling a {@link FPSet} with max int + 1 random
     */
    @Category(LongTest.class)
    @Test
    public void testMaxFPSetSizeRnd() throws Exception {
        final Random rnd = new Random(RNG_SEED);

        final FPSet fpSet = getFPSetInitialized();

        long predecessor = 0L;

        // fill with max int + 1
        final long l = Integer.MAX_VALUE + 2L;
        for (long i = 1; i < l; i++) {

            // make sure set still contains predecessor
            if (predecessor != 0L) {
                assertTrue(fpSet.contains(predecessor));
            }

            predecessor = rnd.nextLong();
            assertFalse(fpSet.put(predecessor));
            final long currentSize = fpSet.size();
            assertEquals(i, currentSize);

            printInsertionSpeed(fpSet);
        }

        // try creating a check point
        fpSet.beginChkpt();
        fpSet.commitChkpt();

        endTimeStamp = new Date();

        assertTrue(fpSet.checkInvariant());

        //
        assertEquals(l - 1, fpSet.size());
    }

    /**
     * Test filling a {@link FPSet} with max int + 1
     */
    @Category(LongTest.class)
    @Test
    public void testMaxFPSetSize() throws Exception {

        //
        final FPSet fpSet = getFPSet(new FPSetConfiguration());
        fpSet.init(1, tmpdir, filename);

        long counter = 0;
        // fill with max int + 1
        final long l = Integer.MAX_VALUE + 2L;
        // choose value in the interval [-l/2, l/2]
        for (long i = (l / 2) * -1; i < l; i++) {

            long value = -1;
            if (i % 2 != 0) {
                value = l - i;
            } else {
                value = i;
            }

            assertFalse(fpSet.put(value));
            final long currentSize = fpSet.size();
            assertEquals(++counter, currentSize);

            printInsertionSpeed(fpSet);
        }

        // try creating a check point
        fpSet.beginChkpt();
        fpSet.commitChkpt();

        //
        assertEquals(l, fpSet.size());
    }
}
