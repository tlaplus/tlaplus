/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool.fp;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.tool.fp.OffHeapDiskFPSet.ConcurrentOffHeapMSBFlusher;

public class OffHeapDiskFPSetFlusherReuseTest {

	// 8192 / 1 > 2 * PROBE_LIMIT, so eviction with one thread selects a
	// ConcurrentOffHeapMSBFlusher, whose executor the merge shuts down.
	private static final int SLOTS = 8192;

	private static OffHeapDiskFPSet newEvictedFPSet(final String name) throws IOException {
		final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + name
				+ System.currentTimeMillis();
		new File(tmpdir).mkdirs();

		final DummyFPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
		fpSetConfig.setMemoryInFingerprintCnt(SLOTS);
		final OffHeapDiskFPSet fpSet = new OffHeapDiskFPSet(fpSetConfig);
		fpSet.init(1, tmpdir, name);

		assertFalse(fpSet.put(41L));
		assertFalse(fpSet.put(97L));
		// Call evict directly instead of through the static OffHeapSynchronizer,
		// which keeps the sets of other tests registered after close.
		fpSet.evict();

		assertFalse(fpSet.put(131L));
		assertFalse(fpSet.put(197L));
		return fpSet;
	}

	private static void assertContainsAll(final OffHeapDiskFPSet fpSet) throws IOException {
		assertTrue(fpSet.contains(41L));
		assertTrue(fpSet.contains(97L));
		assertTrue(fpSet.contains(131L));
		assertTrue(fpSet.contains(197L));
	}

	@Test
	public void testCheckFPsAfterConcurrentEviction() throws Exception {
		final int oldWorkers = TLCGlobals.getNumWorkers();
		final OffHeapDiskFPSet fpSet = newEvictedFPSet("FlusherReuseCheckFPs");
		try {
			// floor(8192 / 48) <= 2 * PROBE_LIMIT, so checkFPs does not qualify
			// for a new concurrent flusher.
			TLCGlobals.setNumWorkers(48);
			fpSet.checkFPs();
			assertContainsAll(fpSet);
		} finally {
			TLCGlobals.setNumWorkers(oldWorkers);
			fpSet.close();
		}
	}

	@Test
	public void testDefaultFlusherSurvivesConcurrentEviction() throws Exception {
		final OffHeapDiskFPSet fpSet = newEvictedFPSet("FlusherReuseDefault");
		try {
			// DiskFPSet#recover(TLCTrace) and DiskFPSet#checkInvariant call
			// this.flusher directly.
			assertFalse(fpSet.flusher instanceof ConcurrentOffHeapMSBFlusher);
		} finally {
			fpSet.close();
		}
	}

	@Test
	public void testCheckInvariantAfterConcurrentEviction() throws Exception {
		final OffHeapDiskFPSet fpSet = newEvictedFPSet("FlusherReuseCheckInvariant");
		try {
			assertTrue(fpSet.checkInvariant(4L));
			assertContainsAll(fpSet);
		} finally {
			fpSet.close();
		}
	}

	@Test
	public void testSecondEvictionAfterConcurrentEviction() throws Exception {
		final OffHeapDiskFPSet fpSet = newEvictedFPSet("FlusherReuseSecondEviction");
		try {
			fpSet.evict();
			assertContainsAll(fpSet);
		} finally {
			fpSet.close();
		}
	}
}
