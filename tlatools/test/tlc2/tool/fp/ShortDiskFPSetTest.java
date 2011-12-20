// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class ShortDiskFPSetTest extends AbstractFPSetTest {
	
	private static final boolean runKnownFailures = Boolean
			.getBoolean(ShortDiskFPSetTest.class.getName() + ".runKnown");
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(int)
	 */
	protected FPSet getFPSet(int freeMemory) throws IOException {
		final DiskFPSet fpSet = new DiskFPSet(freeMemory);
		fpSet.init(1, tmpdir, filename);
		return fpSet;
	}
	
	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} returns true for zero fp
	 * @throws IOException 
	 */
	public void testWithoutZeroFP() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse("Succeeded to look up 0 fp", fpSet.contains(0l));
	}
	
	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} returns true for min fp
	 * @throws IOException 
	 */
	public void testWithoutMinFP() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse("Succeeded to look up 0 fp", fpSet.contains(Long.MIN_VALUE));
	}
	
	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} returns true for max fp
	 * @throws IOException 
	 */
	public void testWithoutMaxFP() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse("Succeeded to look up 0 fp", fpSet.contains(Long.MAX_VALUE));
	}
	
	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} accepts a 0 fp
	 * @throws IOException 
	 */
	public void testZeroFP() throws IOException {
		// skip known failures which aren't likely to be fixed anytime soon
		// @see https://bugzilla.tlaplus.net/show_bug.cgi?id=213
		if(!runKnownFailures) {
			System.out
					.println("Skipping test failing due to https://bugzilla.tlaplus.net/show_bug.cgi?id=213");
			return;
		}

		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.put(0l));
		assertTrue("Failed to look up 0 fp", fpSet.contains(0l));
	}
	
	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} accepts a min fp
	 * @throws IOException 
	 */
	public void testMinFP() throws IOException {
		// skip known failures which aren't likely to be fixed anytime soon
		// @see https://bugzilla.tlaplus.net/show_bug.cgi?id=213
		if(!runKnownFailures) {
			System.out
					.println("Skipping test failing due to https://bugzilla.tlaplus.net/show_bug.cgi?id=213");
			return;
		}
		
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		// zeroing the msb in DiskFPSet turns Long.Min_Value into 0
		assertFalse(fpSet.put(Long.MIN_VALUE));
		assertTrue("Failed to look up min fp", fpSet.contains(Long.MIN_VALUE));
	}
	
	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} accepts a min - 1  fp
	 * @throws IOException 
	 */
	public void testMinMin1FP() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		// zeroing the msb in DiskFPSet turns Long.Min_Value into 0
		assertFalse(fpSet.put(Long.MIN_VALUE - 1l));
		assertTrue("Failed to look up min fp", fpSet.contains(Long.MIN_VALUE - 1l));
	}


	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} accepts a -1 fp
	 * @throws IOException 
	 */
	public void testNeg1FP() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.put(-1l));
		assertTrue("Failed to look up min fp", fpSet.contains(-1l));
	}
	
	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} accepts a +1 fp
	 * @throws IOException 
	 */
	public void testPos1FP() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.put(1l));
		assertTrue("Failed to look up min fp", fpSet.contains(1l));
	}

	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} accepts a max fp
	 * @throws IOException 
	 */
	public void testMaxFP() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.put(Long.MAX_VALUE));
		assertTrue("Failed to look up max fp", fpSet.contains(Long.MAX_VALUE));
	}

	/**
	 * Tries to call
	 * {@link DiskFPSet#calculateMidEntry(long, long, double, long, long)} with
	 * values causing a negative midEntry to be calculated.
	 * 
	 * @throws IOException
	 */
	public void testValues() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());

		final List<Long> loVals = new ArrayList<Long>();
		// no negative values (MSB stripped in DiskFPSet)
		// loVals.add(Long.MIN_VALUE);
		// loVals.add(Long.MIN_VALUE - 1l);
		// loVals.add(Long.MIN_VALUE / 2l);
		// loVals.add(-1l);

		loVals.add(0l); // zero valid fp
		loVals.add(1l);
		loVals.add(Long.MAX_VALUE / 2l);
		loVals.add(Long.MAX_VALUE - 1l);
		loVals.add(Long.MAX_VALUE);

		final List<Long> hiVals = new ArrayList<Long>();
		// no negative values (MSB stripped in DiskFPSet)
		// hiVals.add(Long.MIN_VALUE);
		// hiVals.add(Long.MIN_VALUE - 1l);
		// hiVals.add(Long.MIN_VALUE / 2l);
		// hiVals.add(-1l);

		hiVals.add(0l); // zero valid fp
		hiVals.add(1l);
		hiVals.add(Long.MAX_VALUE / 2l);
		hiVals.add(Long.MAX_VALUE - 1l);
		hiVals.add(Long.MAX_VALUE);

		final List<Long> fps = new ArrayList<Long>();
		// no negative values (MSB stripped in DiskFPSet)
		// fps.add(Long.MIN_VALUE);
		// fps.add(Long.MIN_VALUE - 1l);
		// fps.add(Long.MIN_VALUE / 2l);
		// fps.add(-1l);

		fps.add(0l);
		fps.add(1l);
		fps.add(Long.MAX_VALUE / 2l);
		fps.add(Long.MAX_VALUE - 1l);
		fps.add(Long.MAX_VALUE);

		final List<Long> loEntries = new ArrayList<Long>();
		loEntries.add(0l);
		loEntries.add(1l);
		// possible maximum due to impl. detail in DiskFPSet
		// (array index Integer.Max_Value)
		loEntries.add((long) Integer.MAX_VALUE * 1024);
		// theoretically loEntry can go up to Long.MAX_VALUE
		// loEntries.add(Long.MAX_VALUE - 1l);
		// loEntries.add(Long.MAX_VALUE);

		final List<Long> hiEntries = new ArrayList<Long>();
		hiEntries.add(0l);
		hiEntries.add(1l);
		// possible maximum due to impl. detail in DiskFPSet
		// (array index Integer.Max_Value)
		hiEntries.add((long) Integer.MAX_VALUE * 1024);
		// theoretically hiEntry can go up to Long.MAX_VALUE
		// hiEntries.add(Long.MAX_VALUE - 1l);
		// hiEntries.add(Long.MAX_VALUE);

		// loVals
		for (final Iterator<Long> itr0 = loVals.iterator(); itr0.hasNext();) {
			final Long loVal = (Long) itr0.next();
			// hiVals
			for (final Iterator<Long> itr1 = hiVals.iterator(); itr1.hasNext();) {
				final Long hiVal = (Long) itr1.next();
				// fps
				for (final Iterator<Long> itr2 = fps.iterator(); itr2.hasNext();) {
					final Long fp = (Long) itr2.next();
					// loEntry
					for (final Iterator<Long> itr3 = loEntries.iterator(); itr3.hasNext();) {
						final Long loEntry = (Long) itr3.next();
						// hiEntry
						for (final Iterator<Long> itr4 = hiEntries.iterator(); itr4.hasNext();) {
							final Long hiEntry = (Long) itr4.next();
							testCalculateMidEntry(fpSet, loVal, hiVal, fp, loEntry, hiEntry);
						}
					}
				}
			}
		}
	}

	private void testCalculateMidEntry(DiskFPSet fpSet, long loVal, long hiVal, long fp, long loEntry, long hiEntry)
			throws IOException {
		if (!isInvalidInput(loVal, hiVal, fp, loEntry, hiEntry)) {
			try {
				long midEntry = fpSet.calculateMidEntry(loVal, hiVal, fp, loEntry, hiEntry);
				
				assertTrue(getMessage("Negative mid entry", loVal, hiVal, fp, loEntry, hiEntry, midEntry),
						midEntry >= 0);
				assertTrue(getMessage("Not within lower bound", loVal, hiVal, fp, loEntry, hiEntry, midEntry),
						midEntry >= loEntry);
				assertTrue(getMessage("Not within upper bound", loVal, hiVal, fp, loEntry, hiEntry, midEntry),
						midEntry <= hiEntry);
				
				// DiskFPSet#diskLookup uses long addressing and thus has to multiply by 8 
				assertTrue(getMessage("midEntry turned negative", loVal, hiVal, fp, loEntry, hiEntry, midEntry),
						(midEntry * 8) >= 0);
				
			} catch (RuntimeException e) {
				fail("failed to calculate for valid input (loVal, hiVal, fp, loEntry, hiEntry): " + loVal + ", "
						+ hiVal + ", " + fp + ", " + loEntry + ", " + hiEntry);
			}
		}
	}

	private String getMessage(String txt, long loVal, long hiVal, long fp, long loEntry, long hiEntry, long midEntry) {
		return txt + " (loVal, hiVal, fp, loEntry, hiEntry, midEntry): " + loVal + ", "
				+ hiVal + ", " + fp + ", " + loEntry + ", " + hiEntry + ", " + midEntry;
	}

	private boolean isInvalidInput(long loVal, long hiVal, long fp, long loEntry, long hiEntry) {
		return loVal > hiVal || loVal > fp || hiVal < fp || loEntry >= hiEntry;
	}
	
	/**
	 * Tests if {@link DiskFPSet#diskLookup(long)} returns true for a fp that is
	 * first fp in first page
	 * 
	 * page size hard-coded in {@link DiskFPSet} to be 1024
	 * 
	 * @throws IOException 
	 */
	public void testDiskLookupWithFpOnLoPage() throws IOException {
		int freeMemory = 1000; // causes 16 in memory entries
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(freeMemory);
		
		// add enough fps to cause 3 disk writes
		final long fp = 1l;
		for (long i = 0; i < 1024 * 3; i++) {
			assertFalse(fpSet.put(fp + i));
			assertTrue(fpSet.contains(fp + i));
		}
		
		assertTrue("Failed to lookup fp on first page", fpSet.diskLookup(fp));
	}
	
	/**
	 * Tests how {@link DiskFPSet#memLookup(long)} handles zeros
	 * 
	 * @throws IOException 
	 */
	public void testMemLookupWithZeros() throws IOException {
		// skip known failures which aren't likely to be fixed anytime soon
		// @see https://bugzilla.tlaplus.net/show_bug.cgi?id=213
		if(!runKnownFailures) {
			System.out
					.println("Skipping test failing due to https://bugzilla.tlaplus.net/show_bug.cgi?id=213");
			return;
		}
		
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.memInsert(0l));
		assertFalse(fpSet.diskLookup(0l));
		assertTrue(fpSet.memLookup(0l));
	}
	
	/**
	 * Tests how {@link DiskFPSet#memLookup(long)} handles Long.Min_VALUE
	 * 
	 * @throws IOException 
	 */
	public void testMemLookupWithMin() throws IOException {
		// skip known failures which aren't likely to be fixed anytime soon
		// @see https://bugzilla.tlaplus.net/show_bug.cgi?id=213
		if(!runKnownFailures) {
			System.out
					.println("Skipping test failing due to https://bugzilla.tlaplus.net/show_bug.cgi?id=213");
			return;
		}
		
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.memInsert(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
		assertFalse(fpSet.diskLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
		assertTrue(fpSet.memLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
	}
	
	/**
	 * Tests how {@link DiskFPSet#memLookup(long)} handles MAx_Value
	 * 
	 * @throws IOException 
	 */
	public void testMemLookupWithMax() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.memInsert(Long.MAX_VALUE));
		assertFalse(fpSet.diskLookup(Long.MAX_VALUE));
		assertTrue(fpSet.memLookup(Long.MAX_VALUE));
	}

	/**
	 * Tests how {@link DiskFPSet#memLookup(long)} handles zeros
	 * 
	 * @throws IOException 
	 */
	public void testDiskLookupWithZeros() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.memInsert(0l));
		assertFalse(fpSet.diskLookup(0l));
		fpSet.flushTable();
		assertTrue(fpSet.diskLookup(0l));
		// undefined behavior
		// assertTrue(fpSet.memLookup(0l));
	}
	
	/**
	 * Tests how {@link DiskFPSet#memLookup(long)} handles Long.Min_VALUE
	 * 
	 * @throws IOException 
	 */
	public void testDiskLookupWithMin() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.memInsert(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
		assertFalse(fpSet.diskLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
		fpSet.flushTable();
		assertTrue(fpSet.diskLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
		// undefined behavior
		// assertTrue(fpSet.memLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
	}
	
	/**
	 * Tests how {@link DiskFPSet#memLookup(long)} handles MAx_Value
	 * 
	 * @throws IOException 
	 */
	public void testDiskLookupWithMax() throws IOException {
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(getFreeMemory());
		assertFalse(fpSet.memInsert(Long.MAX_VALUE));
		assertFalse(fpSet.diskLookup(Long.MAX_VALUE));
		fpSet.flushTable();
		assertTrue(fpSet.diskLookup(Long.MAX_VALUE));
		assertTrue(fpSet.memLookup(Long.MAX_VALUE));
	}

	/**
	 * Tests how {@link DiskFPSet#diskLookup(long)} handles max on pages
	 * 
	 * @throws IOException 
	 */
	public void testDiskLookupWithMaxOnPage() throws IOException {
		testDiskLookupOnPage(Long.MAX_VALUE);
	}

	/**
	 * Tests how {@link DiskFPSet#diskLookup(long)} handles zeros on pages
	 * 
	 * @throws IOException 
	 */
	public void testDiskLookupWithZerosOnPage() throws IOException {
		// skip known failures which aren't likely to be fixed anytime soon
		// @see https://bugzilla.tlaplus.net/show_bug.cgi?id=213
		if(!runKnownFailures) {
			System.out
					.println("Skipping test failing due to https://bugzilla.tlaplus.net/show_bug.cgi?id=213");
			return;
		}
		testDiskLookupOnPage(0l);
	}

	/**
	 * Tests how {@link DiskFPSet#diskLookup(long)} handles Long#Min_Value on pages
	 * 
	 * @throws IOException 
	 */
	public void testDiskLookupWithLongMinValueOnPage() throws IOException {
		// skip known failures which aren't likely to be fixed anytime soon
		// @see https://bugzilla.tlaplus.net/show_bug.cgi?id=213
		if(!runKnownFailures) {
			System.out
					.println("Skipping test failing due to https://bugzilla.tlaplus.net/show_bug.cgi?id=213");
			return;
		}
		
		testDiskLookupOnPage(Long.MIN_VALUE);
	}

	private void testDiskLookupOnPage(final long fp) throws IOException {
		int freeMemory = 1000; // causes 16 in memory entries
		final DiskFPSet fpSet = (DiskFPSet) getFPSet(freeMemory);
		
		// add enough fps to cause 2 disk writes
		assertFalse(fpSet.put(fp));
		for (long i = 1; i < 1024 * 2; i++) {
			assertTrue("Failed to add fingerprint", fpSet.put(fp));
			assertTrue(fpSet.contains(fp));
		}
		
		final long fp0 = fp & 0x7FFFFFFFFFFFFFFFL;
		assertTrue(fpSet.memLookup(fp));
		assertFalse(fpSet.diskLookup(fp0));
	}
}
