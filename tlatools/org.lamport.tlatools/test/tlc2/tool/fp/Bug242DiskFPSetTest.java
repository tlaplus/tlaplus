// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.fail;

/**
 *
 */
public class Bug242DiskFPSetTest extends AbstractFPSetTest {

    /* (non-Javadoc)
     * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(int)
     */
    @Override
    protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException {
        return new DummyDiskFPSet(fpSetConfig);
    }

    @SuppressWarnings("deprecation")
    private FPSet getFPSet(final int mem) throws IOException {
        final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
        fpSetConfiguration.setMemory(mem);
        fpSetConfiguration.setRatio(1.0d);
        return getFPSet(fpSetConfiguration);
    }

    /**
     * @see <a href="../../general/bugzilla/index.html">Bug #242</a>
     */
    @Test
    public void testDiskFPSetWithHighMem() {
        try {
            getFPSet(2097153638);
        } catch (final OutOfMemoryError e) {
            // valid case
        } catch (final Exception e) {
            fail(e.getMessage());
        }
    }

    @Test
    public void testDiskFPSetIntMaxValue() {
        try {
            getFPSet(Integer.MAX_VALUE);
        } catch (final OutOfMemoryError e) {
            // valid case
        } catch (final Exception e) {
            fail(e.getMessage());
        }
    }

    @Test
    public void testDiskFPSetIntMinValue() {
        try {
            getFPSet(Integer.MIN_VALUE);
        } catch (final Exception e) {
            // expected to be invalid
            return;
        }
        fail();
    }

    @Test
    public void testDiskFPSetZero() {
        try {
            var fpSet = getFPSet(0);
            fpSet.close();
        } catch (final Exception e) {
            fail(e.getMessage());
        }
    }

    @Test
    public void testDiskFPSetOne() {
        try {
            var fpSet = getFPSet(1);
            fpSet.close();
        } catch (final Exception e) {
            fail(e.getMessage());
        }
    }
}
