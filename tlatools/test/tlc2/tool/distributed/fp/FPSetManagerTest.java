/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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

package tlc2.tool.distributed.fp;

import java.io.File;
import java.io.IOException;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import tlc2.tool.distributed.fp.FPSetManager.FPSets;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;

public class FPSetManagerTest {

	protected static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "FPSetTest"
			+ System.currentTimeMillis();

	@Before
	public void before() {
		new File(tmpdir).mkdirs();
	}

	@Test
	public void test2() throws IOException {
		doTest(2);
	}

	@Test
	public void test3() throws IOException {
		doTest(3);
	}

	@Test
	public void test4() throws IOException {
		doTest(4);
	}

	@Test
	public void test5() throws IOException {
		doTest(5);
	}

	@Test
	public void test8() throws IOException {
		doTest(8);
	}

	private void doTest(int expectedNumOfServers) throws RemoteException, IOException, FPSetManagerException {
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setFpBits(1); // two nested FPSets

		final List<FPSets> sets = new ArrayList<FPSets>();
		for (int i = 0; i < fpSetConfiguration.getMultiFPSetCnt(); i++) {
			final FPSet fpSet = FPSetFactory.getFPSet(fpSetConfiguration);
			fpSet.init(1, tmpdir, "test" + expectedNumOfServers);
			sets.add(new FPSets(fpSet, "localhost" + i));
		}

		final IFPSetManager manager = new DynamicFPSetManager(expectedNumOfServers);
		for (FPSets fpSets : sets) {
			manager.register(fpSets.getFpset(), fpSets.getFpset().toString());
		}

		// Index uses LSBs
		Assert.assertEquals(0, manager.getFPSetIndex(0));
		Assert.assertEquals(1, manager.getFPSetIndex(1));
		Assert.assertEquals(0, manager.getFPSetIndex(2));
		Assert.assertEquals(1, manager.getFPSetIndex(3));
		Assert.assertEquals(0, manager.getFPSetIndex((1L << 63) + 2L));
		Assert.assertEquals(1, manager.getFPSetIndex((1L << 63) + 1L));

		final Set<Long> fps = new HashSet<Long>();
		// fps.add(0L); // Not accepted by nested FPSets
		fps.add(1L);              // 00...0001
		fps.add((1L << 62) + 1L); // 01...0001
		fps.add((1L << 63) + 1L); // 10...0001
		fps.add((3L << 62) + 1L); // 11...0001
		fps.add(2L);              // 00...0010
		fps.add((1L << 62) + 2L); // 01...0010
		fps.add((1L << 63) + 2L); // 10...0010
		fps.add((3L << 62) + 2L); // 11...0010
		fps.add(3L);              // 00...0011
		fps.add((1L << 62) + 3L); // 01...0011
		fps.add((1L << 63) + 3L); // 10...0011
		fps.add((3L << 62) + 3L); // 11...0011
		fps.add(4L);              // 00...0100
		fps.add((1L << 62) + 4L); // 01...0100
		fps.add((1L << 63) + 4L); // 10...0100
		fps.add((3L << 62) + 4L); // 11...0100
		fps.add(5L);              // 00...0101
		fps.add((1L << 62) + 5L); // 01...0101
		fps.add((1L << 63) + 5L); // 10...0101
		fps.add((3L << 62) + 5L); // 11...0101
		fps.add(6L);              // 00...0110
		fps.add((1L << 62) + 6L); // 01...0110
		fps.add((1L << 63) + 6L); // 10...0110
		fps.add((3L << 62) + 6L); // 11...0110
		fps.add(7L);              // 00...0110
		fps.add((1L << 62) + 7L); // 01...0111
		fps.add((1L << 63) + 7L); // 10...0111
		fps.add((3L << 62) + 7L); // 11...0111
		fps.add(8L);              // 00...1000
		fps.add((1L << 62) + 8L); // 01...1000
		fps.add((1L << 63) + 8L); // 10...1000
		fps.add((3L << 62) + 8L); // 11...1000

		final Set<Long> unseen = new HashSet<Long>(fps);
		for (Long fp : fps) {
			// Unseen fingerprints must not be in set.
			for (Long unseenFP : unseen) {
				Assert.assertFalse(manager.contains(unseenFP));
			}
			Assert.assertTrue(unseen.remove(fp));

			Assert.assertFalse(printBinaryString("", fp), manager.put(fp));
			Assert.assertTrue(printBinaryString("", fp), manager.contains(fp));
		}

		Assert.assertEquals(fps.size(), manager.size());

		Assert.assertTrue(manager.checkInvariant());
	}

	private String printBinaryString(final String id, final long a) {
		return String.format(id + ":%64s", Long.toBinaryString(a)).replace(' ', '0');
	}
}
