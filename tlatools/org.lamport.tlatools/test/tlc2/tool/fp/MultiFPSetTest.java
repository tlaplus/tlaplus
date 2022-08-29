// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.fail;

/**
 * @author Markus Alexander Kuppe
 */
public class MultiFPSetTest {

    protected static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "MultiFPSetTest"
            + System.currentTimeMillis();

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    @Before
    public void setUp() {
        new File(tmpdir).mkdirs();
    }

    /**
     * Test method for {@link tlc2.tool.fp.MultiFPSet#MultiFPSet}.
     *
     * @throws Exception Not supposed to happen
     */
    @Test
    public void testCTorLowerMin() throws Exception {
        System.setProperty(FPSetFactory.IMPL_PROPERTY, MemFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();

        conf.setFpBits(0);

        try (var fpSet = new MultiFPSet(conf)) {
        } catch (final RuntimeException e) {
            return;
        }
        fail("Negative fpbits must fail");
    }

    /**
     * Test method for {@link tlc2.tool.fp.MultiFPSet#MultiFPSet}.
     *
     * @throws Exception Not supposed to happen
     */
    @Test
    public void testCTorMin() throws Exception {
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        try (var fpSet = new MultiFPSet(conf)) {

        } catch (final RuntimeException e) {
            fail();
        }

    }

    /**
     * Test method for {@link tlc2.tool.fp.MultiFPSet#MultiFPSet}.
     *
     * @throws Exception Not supposed to happen
     */
    @Test
    public void testCTorMax() throws Exception {
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(30);

        try (var fpSet = new MultiFPSet(conf)) {

        } catch (final OutOfMemoryError e) {
            // might happen depending on test machine setup
        } catch (final IllegalArgumentException e) {
            // Happens when MultiFPSetConfiguration is invalid (too many fpsets
            // leaving no room/memory for each individual fpset).
            if (e.getMessage().equals("Given fpSetConfig results in zero or negative fp count.")) {
                return;
            }
            // some other cause for the IAE
            fail();
        } catch (final RuntimeException e) {
            fail();
        }
    }

    /**
     * Test method for {@link tlc2.tool.fp.MultiFPSet#MultiFPSet}.
     */
    @Test
    public void testCTorHigherMax() {
        try {
            final FPSetConfiguration conf = new FPSetConfiguration();
            conf.setFpBits(31);
        } catch (final RuntimeException e) {
            return;
        }
        fail();
    }

    /**
     * Test method for {@link tlc2.tool.fp.MultiFPSet#put(long)}.
     *
     * @throws Exception Not supposed to happen
     */
    @Test
    public void testPutMax() throws Exception {
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        // put a random fp value into set
        try (MultiFPSet mfps = new MultiFPSet(conf)) {
            mfps.put(Long.MAX_VALUE);
        } catch (final ArrayIndexOutOfBoundsException e) {
            fail();
        }
    }

    /**
     * Test method for {@link tlc2.tool.fp.MultiFPSet#put(long)}.
     *
     * @throws Exception Not supposed to happen
     */
    @Test
    public void testPutMin() throws Exception {
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        // put a random fp value into set
        try (MultiFPSet mfps = new MultiFPSet(conf)) {
            mfps.put(Long.MIN_VALUE);
        } catch (final ArrayIndexOutOfBoundsException e) {
            fail();
        }
    }

    /**
     * Test method for {@link tlc2.tool.fp.MultiFPSet#put(long)}.
     *
     * @throws Exception Not supposed to happen
     */
    @Test
    public void testPutZero() throws Exception {
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        // put a random fp value into set
        try (MultiFPSet mfps = new MultiFPSet(conf)) {
            mfps.put(0);
        } catch (final ArrayIndexOutOfBoundsException e) {
            fail();
        }
    }

    @Test
    public void testGetFPSet() throws Exception {
        System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSet");

        final long a = (1L << 62) + 1; // 01...0
        printBinaryString("a01...1", a);
        final long b = 1L; // 0...1
        printBinaryString("b00...1", b);

        final FPSet aFPSet = mfps.getFPSet(a);
        Assert.assertSame(aFPSet, mfps.getFPSet(b));

        // Initially neither a nor b are in the set.
        Assert.assertFalse(aFPSet.contains(a));

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));

        // Add a to the set and verify it's in the
        // set and b isn't.
        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));

        // Add b to the set as well. Now both
        // are supposed to be set members.
        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));

        Assert.assertTrue(aFPSet.contains(a));
        Assert.assertTrue(aFPSet.contains(b));
        Assert.assertEquals(2, aFPSet.size());

        // Get the other FPSet
        final FPSet[] fpSets = mfps.getFPSets();
        final Set<FPSet> s = new HashSet<>();
        Collections.addAll(s, fpSets);
        s.remove(aFPSet);
        final FPSet bFPSet = (FPSet) s.toArray()[0];

        Assert.assertFalse(bFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(b));
        Assert.assertEquals(0, bFPSet.size());

        Assert.assertTrue(mfps.checkInvariant());

        mfps.close();
    }

    @Test
    public void testGetFPSet0() throws Exception {
        System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSet0");

        final long a = (1L << 63) + 1; // 10...1
        printBinaryString("a1...1", a);
        final long b = 1L;             // 00...1
        printBinaryString("b0...1", b);
        final long c = (1L << 62) + 1; // 01...1
        printBinaryString("c1...1", c);
        final long d = (3L << 62) + 1; // 11...1
        printBinaryString("d0...1", d);

        final FPSet aFPSet = mfps.getFPSet(a);
        final FPSet bFPSet = mfps.getFPSet(b);
        Assert.assertNotSame(aFPSet, bFPSet);

        // Initially neither a nor b are in the set.
        Assert.assertFalse(aFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(b));

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        // Add a to the set and verify it's in the
        // set and b isn't.
        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        // Add b to the set as well. Now both
        // are supposed to be set members.
        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(c));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(d));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertTrue(mfps.contains(d));

        for (final FPSet fpSet : mfps.getFPSets()) {
            Assert.assertEquals(2, fpSet.size());
            // Expect to have two buckets
            Assert.assertEquals(2, ((FPSetStatistic) fpSet).getTblLoad());
        }

        Assert.assertTrue(mfps.checkInvariant());

        mfps.close();
    }

    @Test
    public void testGetFPSet1() throws Exception {
        System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(2);
        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSet1");

        final long a = 1L; // 00...1
        printBinaryString("a02", a);
        final long b = (1L << 62) + 1; // 01...1
        printBinaryString("b02", b);
        final long c = (1L << 63) + 1; // 10...1
        printBinaryString("c02", c);
        final long d = (3L << 62) + 1; // 11...1
        printBinaryString("d02", d);

        final Set<FPSet> s = new HashSet<>();
        final FPSet aFPSet = mfps.getFPSet(a);
        s.add(aFPSet);
        final FPSet bFPSet = mfps.getFPSet(b);
        s.add(bFPSet);
        final FPSet cFPSet = mfps.getFPSet(c);
        s.add(cFPSet);
        final FPSet dFPSet = mfps.getFPSet(d);
        s.add(dFPSet);
        Assert.assertEquals(4, s.size());

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(c));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(d));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertTrue(mfps.contains(d));

        for (final FPSet fpSet : s) {
            Assert.assertEquals(1, fpSet.size());
            // Expect to have two buckets
            Assert.assertEquals(1, ((FPSetStatistic) fpSet).getTblLoad());
        }

        // a & c and b & d have collisions at the individual DiskFPSet level.
        Assert.assertTrue(aFPSet.contains(a));
        Assert.assertFalse(aFPSet.contains(b));
        Assert.assertTrue(aFPSet.contains(c)); // expected collision
        Assert.assertFalse(aFPSet.contains(d));

        Assert.assertTrue(bFPSet.contains(b));
        Assert.assertFalse(bFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(c));
        Assert.assertTrue(bFPSet.contains(d)); // expected collision

        Assert.assertTrue(cFPSet.contains(c));
        Assert.assertFalse(cFPSet.contains(b));
        Assert.assertTrue(cFPSet.contains(a)); // expected collision
        Assert.assertFalse(cFPSet.contains(d));

        Assert.assertTrue(dFPSet.contains(d));
        Assert.assertTrue(dFPSet.contains(b)); // expected collision
        Assert.assertFalse(dFPSet.contains(c));
        Assert.assertFalse(dFPSet.contains(a));

        Assert.assertTrue(mfps.checkInvariant());

        mfps.close();
    }

    @Test
    public void testGetFPSetL() throws Exception {
        System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSetL");

        final long a = (1L << 62) + 1;
        printBinaryString("a01", a);
        final long b = 1L;
        printBinaryString("b01", b);

        final FPSet aFPSet = mfps.getFPSet(a);
        Assert.assertSame(aFPSet, mfps.getFPSet(b));

        // Initially neither a nor b are in the set.
        Assert.assertFalse(aFPSet.contains(a));

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));

        // Add a to the set and verify it's in the
        // set and b isn't.
        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));

        // Add b to the set as well. Now both
        // are supposed to be set members.
        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));

        Assert.assertTrue(aFPSet.contains(a));
        Assert.assertTrue(aFPSet.contains(b));
        Assert.assertEquals(2, aFPSet.size());

        // Get the other FPSet
        final FPSet[] fpSets = mfps.getFPSets();
        final Set<FPSet> s = new HashSet<>();
        Collections.addAll(s, fpSets);
        s.remove(aFPSet);
        final FPSet bFPSet = (FPSet) s.toArray()[0];

        Assert.assertFalse(bFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(b));
        Assert.assertEquals(0, bFPSet.size());

        Assert.assertTrue(mfps.checkInvariant());

        mfps.close();
    }

    @Test
    public void testGetFPSet0L() throws Exception {
        System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSet0L");

        final long a = (1L << 63) + 1;
        printBinaryString("a01", a);
        final long b = 1L;
        printBinaryString("b01", b);

        final FPSet aFPSet = mfps.getFPSet(a);
        final FPSet bFPSet = mfps.getFPSet(b);
        Assert.assertNotSame(aFPSet, bFPSet);

        // Initially neither a nor b are in the set.
        Assert.assertFalse(aFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(b));

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));

        // Add a to the set and verify it's in the
        // set and b isn't.
        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));

        // Add b to the set as well. Now both
        // are supposed to be set members.
        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));

        Assert.assertTrue(mfps.checkInvariant());

        mfps.close();
    }

    @Test
    public void testGetFPSet1L() throws Exception {
        System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(2);
        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSet1L");

        final long a = 1L; // 00...1
        printBinaryString("a02", a);
        final long b = (1L << 62) + 1; // 01...1
        printBinaryString("b02", b);
        final long c = (1L << 63) + 1; // 10...1
        printBinaryString("c02", c);
        final long d = (3L << 62) + 1; // 11...1
        printBinaryString("d02", d);

        final Set<FPSet> s = new HashSet<>();
        final FPSet aFPSet = mfps.getFPSet(a);
        s.add(aFPSet);
        final FPSet bFPSet = mfps.getFPSet(b);
        s.add(bFPSet);
        final FPSet cFPSet = mfps.getFPSet(c);
        s.add(cFPSet);
        final FPSet dFPSet = mfps.getFPSet(d);
        s.add(dFPSet);
        Assert.assertEquals(4, s.size());

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(c));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(d));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertTrue(mfps.contains(d));

        for (final FPSet fpSet : s) {
            Assert.assertEquals(1, fpSet.size());
        }

        // a & c and b & d have collisions at the individual DiskFPSet level.
        Assert.assertTrue(aFPSet.contains(a));
        Assert.assertFalse(aFPSet.contains(b));
        Assert.assertTrue(aFPSet.contains(c)); // expected collision
        Assert.assertFalse(aFPSet.contains(d));

        Assert.assertTrue(bFPSet.contains(b));
        Assert.assertFalse(bFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(c));
        Assert.assertTrue(bFPSet.contains(d)); // expected collision

        Assert.assertTrue(cFPSet.contains(c));
        Assert.assertFalse(cFPSet.contains(b));
        Assert.assertTrue(cFPSet.contains(a)); // expected collision
        Assert.assertFalse(cFPSet.contains(d));

        Assert.assertTrue(dFPSet.contains(d));
        Assert.assertTrue(dFPSet.contains(b)); // expected collision
        Assert.assertFalse(dFPSet.contains(c));
        Assert.assertFalse(dFPSet.contains(a));

        Assert.assertTrue(mfps.checkInvariant());

        mfps.close();
    }

    @Test
    public void testGetFPSetOffHeap() throws Exception {
        if (!System.getProperty("sun.arch.data.model").equals("64")) {
            // LongArray only works on 64bit architectures. See comment in
            // LongArray ctor.
            return;
        }
        System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSetOffHeap");

        final long a = (1L << 62) + 1; // 01...0
        printBinaryString("a01...1", a);
        final long b = 1L; // 0...1
        printBinaryString("b00...1", b);

        final FPSet aFPSet = mfps.getFPSet(a);
        Assert.assertSame(aFPSet, mfps.getFPSet(b));

        // Initially neither a nor b are in the set.
        Assert.assertFalse(aFPSet.contains(a));

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));

        // Add a to the set and verify it's in the
        // set and b isn't.
        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));

        // Add b to the set as well. Now both
        // are supposed to be set members.
        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));

        Assert.assertTrue(aFPSet.contains(a));
        Assert.assertTrue(aFPSet.contains(b));
        Assert.assertEquals(2, aFPSet.size());

        // Get the other FPSet
        final FPSet[] fpSets = mfps.getFPSets();
        final Set<FPSet> s = new HashSet<>();
        Collections.addAll(s, fpSets);
        s.remove(aFPSet);
        final FPSet bFPSet = (FPSet) s.toArray()[0];

        Assert.assertFalse(bFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(b));
        Assert.assertEquals(0, bFPSet.size());

        Assert.assertTrue(mfps.checkInvariant());

        mfps.close();
    }

    @Test
    public void testGetFPSetOffHeap0() throws Exception {
        if (!System.getProperty("sun.arch.data.model").equals("64")) {
            // LongArray only works on 64bit architectures. See comment in
            // LongArray ctor.
            return;
        }
        System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(1);

        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSetOffHeap0");

        final long a = (1L << 63) + 1; // 10...1
        printBinaryString("a1...1", a);
        final long b = 1L;             // 00...1
        printBinaryString("b0...1", b);
        final long c = (1L << 62) + 1; // 01...1
        printBinaryString("c1...1", c);
        final long d = (3L << 62) + 1; // 11...1
        printBinaryString("d0...1", d);

        final FPSet aFPSet = mfps.getFPSet(a);
        final FPSet bFPSet = mfps.getFPSet(b);
        Assert.assertNotSame(aFPSet, bFPSet);

        // Initially neither a nor b are in the set.
        Assert.assertFalse(aFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(b));

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        // Add a to the set and verify it's in the
        // set and b isn't.
        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        // Add b to the set as well. Now both
        // are supposed to be set members.
        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(c));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(d));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertTrue(mfps.contains(d));

        for (final FPSet fpSet : mfps.getFPSets()) {
            Assert.assertEquals(2, fpSet.size());
            // Expect to have two buckets
            Assert.assertEquals(2, ((FPSetStatistic) fpSet).getTblLoad());
        }

        Assert.assertTrue(mfps.checkInvariant());

        mfps.close();
    }

    @Test
    public void testGetFPSetOffHeap1() throws Exception {
        if (!System.getProperty("sun.arch.data.model").equals("64")) {
            // LongArray only works on 64bit architectures. See comment in
            // LongArray ctor.
            return;
        }
        System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
        final FPSetConfiguration conf = new FPSetConfiguration();
        conf.setFpBits(2);
        final MultiFPSet mfps = new MultiFPSet(conf);
        mfps.init(1, tmpdir, "testGetFPSetOffHeap1");

        final long a = 1L; // 00...1
        printBinaryString("a02", a);
        final long b = (1L << 62) + 1; // 01...1
        printBinaryString("b02", b);
        final long c = (1L << 63) + 1; // 10...1
        printBinaryString("c02", c);
        final long d = (3L << 62) + 1; // 11...1
        printBinaryString("d02", d);

        final Set<FPSet> s = new HashSet<>();
        final FPSet aFPSet = mfps.getFPSet(a);
        s.add(aFPSet);
        final FPSet bFPSet = mfps.getFPSet(b);
        s.add(bFPSet);
        final FPSet cFPSet = mfps.getFPSet(c);
        s.add(cFPSet);
        final FPSet dFPSet = mfps.getFPSet(d);
        s.add(dFPSet);
        Assert.assertEquals(4, s.size());

        Assert.assertFalse(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(a));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertFalse(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(b));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertFalse(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(c));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertFalse(mfps.contains(d));

        Assert.assertFalse(mfps.put(d));
        Assert.assertTrue(mfps.contains(a));
        Assert.assertTrue(mfps.contains(b));
        Assert.assertTrue(mfps.contains(c));
        Assert.assertTrue(mfps.contains(d));

        for (final FPSet fpSet : s) {
            Assert.assertEquals(1, fpSet.size());
            // Expect to have two buckets
            Assert.assertEquals(1, ((FPSetStatistic) fpSet).getTblLoad());
        }

        // a & c and b & d have collisions at the individual DiskFPSet level.
        Assert.assertTrue(aFPSet.contains(a));
        Assert.assertFalse(aFPSet.contains(b));
        Assert.assertTrue(aFPSet.contains(c)); // expected collision
        Assert.assertFalse(aFPSet.contains(d));

        Assert.assertTrue(bFPSet.contains(b));
        Assert.assertFalse(bFPSet.contains(a));
        Assert.assertFalse(bFPSet.contains(c));
        Assert.assertTrue(bFPSet.contains(d)); // expected collision

        Assert.assertTrue(cFPSet.contains(c));
        Assert.assertFalse(cFPSet.contains(b));
        Assert.assertTrue(cFPSet.contains(a)); // expected collision
        Assert.assertFalse(cFPSet.contains(d));

        Assert.assertTrue(dFPSet.contains(d));
        Assert.assertTrue(dFPSet.contains(b)); // expected collision
        Assert.assertFalse(dFPSet.contains(c));
        Assert.assertFalse(dFPSet.contains(a));

        Assert.assertTrue(mfps.checkInvariant());
        mfps.close();
    }

    private void printBinaryString(final String id, final long a) {
//		System.out.println(String.format(id + ":%64s", Long.toBinaryString(a)).replace(' ', '0'));
    }
}
