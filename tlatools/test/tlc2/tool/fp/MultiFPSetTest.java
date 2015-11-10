// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import static org.junit.Assert.fail;

import java.io.IOException;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Markus Alexander Kuppe
 */
public class MultiFPSetTest {

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	@Before
	public void setUp() throws Exception {
	}

	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#new}.
	 * @throws IOException Not supposed to happen
	 */
	@Test
	public void testCTorLowerMin() throws IOException {
		try {
			FPSetConfiguration conf = new FPSetConfiguration();
			conf.setFpBits(0);
			new MultiFPSet(conf);
		} catch (RuntimeException e) {
			return;
		}
		fail("Negative fpbits must fail");
	}
	
	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#new}.
	 * @throws IOException Not supposed to happen
	 */
	@Test
	public void testCTorMin() throws IOException {
		try {
			FPSetConfiguration conf = new FPSetConfiguration();
			conf.setFpBits(1);
			new MultiFPSet(conf);
		} catch (RuntimeException e) {
			fail();
		}
		return;
	}

	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#new}.
	 * @throws IOException Not supposed to happen
	 */
	@Test
	public void testCTorMax() throws IOException {
		try {
			FPSetConfiguration conf = new FPSetConfiguration();
			conf.setFpBits(30);
			new MultiFPSet(conf);
		} catch (OutOfMemoryError e) {
			// might happen depending on test machine setup
			return;
		} catch (IllegalArgumentException e) {
			// Happens when MultiFPSetConfiguration is invalid (too many fpsets
			// leaving no room/memory for each individual fpset).
			if (e.getMessage().equals("Given fpSetConfig results in zero or negative fp count.")) {
				return;
			}
			// some other cause for the IAE
			fail();
		} catch (RuntimeException e) {
			fail();
		}
		return;
	}

	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#new}.
	 * @throws IOException Not supposed to happen
	 */
	@Test
	public void testCTorHigherMax() throws IOException {
		try {
			FPSetConfiguration conf = new FPSetConfiguration();
			conf.setFpBits(31);
			new MultiFPSet(conf);
		} catch (RuntimeException e) {
			return;
		}
		fail();
	}
	
	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#put(long)}.
	 * @throws IOException Not supposed to happen
	 */
	@Test
	public void testPutMax() throws IOException {
		FPSetConfiguration conf = new FPSetConfiguration();
		conf.setFpBits(1);
		final MultiFPSet mfps = new MultiFPSet(conf);

		// put a random fp value into set
		try {
			mfps.put(Long.MAX_VALUE);
		} catch (ArrayIndexOutOfBoundsException e) {
			fail();
		}
	}

	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#put(long)}.
	 * @throws IOException Not supposed to happen
	 */
	@Test
	public void testPutMin() throws IOException {
		FPSetConfiguration conf = new FPSetConfiguration();
		conf.setFpBits(1);
		final MultiFPSet mfps = new MultiFPSet(conf);

		// put a random fp value into set
		try {
			mfps.put(Long.MIN_VALUE);
		} catch (ArrayIndexOutOfBoundsException e) {
			fail();
		}
	}

	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#put(long)}.
	 * @throws IOException Not supposed to happen
	 */
	@Test
	public void testPutZero() throws IOException {
		FPSetConfiguration conf = new FPSetConfiguration();
		conf.setFpBits(1);
		final MultiFPSet mfps = new MultiFPSet(conf);

		// put a random fp value into set
		try {
			mfps.put(0);
		} catch (ArrayIndexOutOfBoundsException e) {
			fail();
		}
	}
}
