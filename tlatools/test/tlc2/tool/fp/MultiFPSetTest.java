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
			new MultiFPSet(0);
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
			new MultiFPSet(1);
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
			new MultiFPSet(30);
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
			new MultiFPSet(31);
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
		final MultiFPSet mfps = new MultiFPSet(1);

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
		final MultiFPSet mfps = new MultiFPSet(1);

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
		final MultiFPSet mfps = new MultiFPSet(1);

		// put a random fp value into set
		try {
			mfps.put(0);
		} catch (ArrayIndexOutOfBoundsException e) {
			fail();
		}
	}
}
