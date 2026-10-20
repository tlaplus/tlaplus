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
import static org.junit.Assert.fail;

import java.io.IOException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.junit.Ignore;
import org.junit.Test;

/**
 * https://github.com/tlaplus/tlaplus/issues/1481
 */
public class Bug1481LSBDiskFPSetTest {

	@SuppressWarnings("deprecation")
	@Ignore("LSBDiskFPSet is unused in practice; TLC fails gracefully with an error message instead (https://github.com/tlaplus/tlaplus/issues/1481)")
	@Test
	public void testMaxTblCntFitsIntoSortBuffer() throws IOException {
		// 40 GiB / 8 bytes per fp / 2.5 auxiliary storage = 2^31 fingerprints.
		final FPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
		fpSetConfig.setMemory(40L << 30);

		final LSBDiskFPSet fpSet = new LSBDiskFPSet(fpSetConfig);

		// LSBFlusher#prepareTable copies all in-memory fingerprints into a single
		// long[], whose length cannot exceed Integer.MAX_VALUE - 8.
		assertTrue("maxTblCnt " + fpSet.getMaxTblCnt() + " does not fit into the LSB sort buffer",
				fpSet.getMaxTblCnt() <= Integer.MAX_VALUE - 8);
	}

	@Test
	public void testFailedFlushReleasesLocks() throws Exception {
		final DummyFPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
		fpSetConfig.setMemoryInFingerprintCnt(1L << 16);

		final LSBDiskFPSet fpSet = new LSBDiskFPSet(fpSetConfig);
		fpSet.init(1, System.getProperty("java.io.tmpdir"), getClass().getCanonicalName());

		for (long fp = 1L; fp <= 1024L; fp++) {
			assertFalse(fpSet.put(fp));
		}

		// Pretend the table holds 2^31 fingerprints so that the next put chooses
		// itself as flusher and LSBFlusher#prepareTable fails.
		final long delta = (1L << 31) - fpSet.getTblCnt();
		fpSet.tblCnt.add(delta);
		try {
			fpSet.put(1025L);
			fail("Expected flush to fail");
		} catch (RuntimeException expected) {
		}
		fpSet.tblCnt.add(-delta);

		assertFalse("Flusher still chosen after failed flush", fpSet.flusherChosen.get());

		// The locks are reentrant, thus another thread has to check that they got
		// released. Lock#lock ignores interrupts, hence a daemon thread.
		final ExecutorService executor = Executors.newSingleThreadExecutor(r -> {
			final Thread t = new Thread(r);
			t.setDaemon(true);
			return t;
		});
		try {
			// Same lock stripe as 1025, which the failed put locked twice.
			final long fp = 1025L + fpSet.getLockCnt();
			final Future<Boolean> put = executor.submit(() -> fpSet.put(fp));
			try {
				assertFalse(put.get(10, TimeUnit.SECONDS));
			} catch (TimeoutException e) {
				fail("Locks still held after failed flush");
			}
		} finally {
			executor.shutdownNow();
		}
	}
}
