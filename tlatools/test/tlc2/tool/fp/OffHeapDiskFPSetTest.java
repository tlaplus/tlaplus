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
package tlc2.tool.fp;

import static tlc2.tool.fp.DiskFPSet.MARK_FLUSHED;
import static tlc2.tool.fp.OffHeapDiskFPSet.EMPTY;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import tlc2.tool.fp.OffHeapDiskFPSet.SortingIterator;

public class OffHeapDiskFPSetTest {
	@Test
	public void testSortingIteratorEmpty() {
		// Create a LongArray and insert known elements.
		final int size = 5;
		final LongArray array = new LongArray(size);
		for (int i = 0; i < size; i++) {
			array.set(i, 0L);
		}
		
		final OffHeapDiskFPSet.Indexer indexer = new OffHeapDiskFPSet.Indexer(size, 1);
		final SortingIterator itr = new OffHeapDiskFPSet.SortingIterator(array, 0L, 0, indexer);

		boolean seen = false;
		try {
			itr.next();
		} catch (NoSuchElementException expected) {
			seen = true;
		}
		Assert.assertTrue(seen);
		Assert.assertFalse(itr.hasNext());
		
		for (int i = 0; i < size; i++) {
			Assert.assertEquals(0L, array.get(i));
		}
	}

	@Test
	public void testSortingIteratorReprobe0() {
		// Create a LongArray and insert known elements.
		final int size = 101;
		final LongArray array = new LongArray(size);
		for (int i = 0; i < size; i++) {
			array.set(i, i+1L); // Cannot insert 0L/EMPTY
		}
		
		// Iterate over array and assert positive elements are returned in sorted order.
		long i = 1L;
		final OffHeapDiskFPSet.Indexer indexer = new OffHeapDiskFPSet.Indexer(size, 1);
		final SortingIterator itr = new OffHeapDiskFPSet.SortingIterator(array, size, 0, indexer);
		while (itr.hasNext()) {
			Assert.assertEquals(i++, itr.next());
		}
		
		// Saw all expected elements?
		Assert.assertFalse(itr.hasNext());
		Assert.assertEquals("Did not read all elements.", size, --i);
		
		// After next, all elements are marked evicted. 
		for (i = 0; i < size; i++) {
			Assert.assertEquals(i + 1L | MARK_FLUSHED, array.get(i));
		}
	}

	@Test
	public void testSortingIteratorReprobe3a() {
		final List<Long> list = new ArrayList<Long>(10);
		list.add(1L);
		list.add(EMPTY);
		list.add(EMPTY);
		list.add(5L);
		list.add(EMPTY);
		list.add(8L);
		list.add(10L);
		list.add(9L);
		list.add(12L);
		list.add(EMPTY);
		doTest(list, 3, 14);
	}
	
	@Test
	public void testSortingIteratorReprobe3b() {
		final List<Long> list = new ArrayList<Long>(10);
		list.add(EMPTY);
		list.add(EMPTY);
		list.add(EMPTY);
		list.add(5L);
		list.add(7L);
		list.add(6L);
		list.add(9L);
		list.add(EMPTY);
		list.add(12L);
		list.add(13L);
		doTest(list, 3, 14);
	}
	
	@Test
	public void testSortingIteratorReprobe3c() {
		final List<Long> list = new ArrayList<Long>(10);
		list.add(1L);
		list.add(2L);
		list.add(-4L);
		list.add(-6L);
		list.add(EMPTY);
		list.add(EMPTY);
		list.add(9L);
		list.add(EMPTY);
		list.add(-12L);
		list.add(EMPTY);
		doTest(list, 3, 14);
	}
	
	@Test
	public void testSortingIteratorReprobe3d() {
		final List<Long> list = new ArrayList<Long>(10);
		list.add(13L);
		list.add(14L);
		list.add(4L);
		list.add(EMPTY);
		list.add(7L);
		list.add(EMPTY);
		list.add(10L);
		list.add(9L);
		list.add(12L);
		list.add(11L);
		doTest(list, 3, 14);
	}
	
	@Test
	public void testSortingIteratorReprobe3e() {
		final List<Long> list = new ArrayList<Long>(10);
		list.add(-1L);
		list.add(-14L);
		list.add(-4L);
		list.add(-5L);
		list.add(EMPTY);
		list.add(7L);
		list.add(EMPTY);
		list.add(EMPTY);
		list.add(-12L);
		list.add(-13L);
		doTest(list, 3, 14);
	}
	
	private static void doTest(final List<Long> list, final int reprobe, final long maxValue) {
		final SortedSet<Long> sorted = new TreeSet<Long>();
		sorted.addAll(list);
		// Remove negative and zero values
		for (long i = (-1 * maxValue); i < 1; i++) {
			sorted.remove(i);
		}
		final Iterator<Long> setIterator = sorted.iterator();
		
		
		// Create a LongArray and insert given elements.
		final LongArray array = new LongArray(list.size());
		long i = 0L;
		for (Long l : list) {
			array.set(i++, l);
		}
		
		// Iterate over array and assert positive elements are returned in sorted order.
		i = 0L;
		final OffHeapDiskFPSet.Indexer indexer = new OffHeapDiskFPSet.Indexer(list.size(), 1, maxValue);
		final SortingIterator itr = new OffHeapDiskFPSet.SortingIterator(array, sorted.size(), reprobe, indexer);
		while (itr.hasNext()) {
			final long expected = setIterator.next();
			Assert.assertEquals(expected, itr.next());
			i++;
		}
		
		// Saw all expected elements
		Assert.assertFalse(itr.hasNext());
		Assert.assertEquals("Failed to read all expected elements.", sorted.size(), i);
		
		// After next, all elements are mark evicted or remain empty. 
		for (i = 0; i < array.size(); i++) {
			Assert.assertTrue(array.get(i) <= EMPTY);
		}
	}
}
