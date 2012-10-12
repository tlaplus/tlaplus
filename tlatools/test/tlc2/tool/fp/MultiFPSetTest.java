// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;

import junit.framework.TestCase;

/**
 * @author Markus Alexander Kuppe
 */
public class MultiFPSetTest extends TestCase {

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
	}

	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#new}.
	 * @throws IOException Not supposed to happen
	 */
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
	public void testCTorMax() throws IOException {
		try {
			FPSetConfiguration conf = new FPSetConfiguration();
			conf.setFpBits(30);
			new MultiFPSet(conf);
		} catch (OutOfMemoryError e) {
			// might happen depending on test machine setup
			return;
		} catch (RuntimeException e) {
			fail();
		}
		return;
	}

	/**
	 * Test method for {@link tlc2.tool.fp.MultiFPSet#new}.
	 * @throws IOException Not supposed to happen
	 */
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
