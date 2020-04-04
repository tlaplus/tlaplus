// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.fail;

import java.io.IOException;

import org.junit.Test;

public class Bug210DiskFPSetTest extends AbstractFPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(int)
	 */
	@Override
	protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException {
		final DummyDiskFPSet fpSet = new DummyDiskFPSet(fpSetConfig);
		fpSet.init(1, tmpdir, filename);
		return fpSet;
	}

	/**
	 * @see Bug #210 in general/bugzilla/index.html
	 * @throws IOException
	 */
	@Test
	public void testDiskLookupWithOverflow() throws IOException {
		// set up an index whose upper bound is beyond 1/1024 of
		// Integer.MAX_VALUE
		//
		// (this calculation is executed in diskLookup to map from in-memory
		// index addresses to on-disk addresses)
		final int size = (Integer.MAX_VALUE / DiskFPSet.NumEntriesPerPage) + 8;
		final long[] anIndex = new long[size];
		anIndex[size - 2] = Long.MAX_VALUE - 3;
		anIndex[size - 1] = Long.MAX_VALUE - 1;

		final DummyDiskFPSet fpSet = (DummyDiskFPSet) getFPSet(new FPSetConfiguration());
		fpSet.setIndex(anIndex);
		
		// do a diskLookup for a non-existent fp that accesses the index values
		// [size - 2, b = size - 1]. These two are "close" to an int overflow if
		// multiplied by 2^10 (DiskFPSet#NumEntriesPerPage).
		try {
			assertFalse(fpSet.diskLookup(Long.MAX_VALUE - 2));
		} catch (IOException e) {
			fail(e.getMessage());
		}
	}
}
