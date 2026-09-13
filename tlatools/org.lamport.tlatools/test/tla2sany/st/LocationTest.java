/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package tla2sany.st;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Iterator;
import java.util.TreeSet;

import org.junit.Test;

public class LocationTest {

	@Test
	public void testContains() {
		assertTrue(new Location(0, 0, 10, 10).includes(new Location(0, 0, 10, 10)));
		assertFalse(new Location(1, 0, 10, 9).includes(new Location(0, 0, 10, 10)));
		
		assertTrue(new Location(0, 0, 10, 10).includes(new Location(1, 0, 10, 9)));
		assertFalse(new Location(1, 0, 10, 9).includes(new Location(0, 0, 10, 10)));
		
		
		Location[] parsedLocations = Location
				.getParsedLocations("line 781, col 31 to line 784, col 68 of module OpenAddressing\n"
						+ "line 783, col 38 to line 784, col 68 of module OpenAddressing\n"
						+ "line 784, col 41 to line 784, col 68 of module OpenAddressing\n"
						
						+ "line 786, col 30 to line 786, col 69 of module OpenAddressing\n"
						+ "line 793, col 29 to line 793, col 63 of module OpenAddressing");
		
		assertTrue(parsedLocations[0].includes(parsedLocations[0]));
		
		assertTrue(parsedLocations[0].includes(parsedLocations[1]));
		assertFalse(parsedLocations[1].includes(parsedLocations[0]));
		
		assertTrue(parsedLocations[0].includes(parsedLocations[2]));
		assertFalse(parsedLocations[2].includes(parsedLocations[0]));

		assertFalse(parsedLocations[0].includes(parsedLocations[3]));
		assertFalse(parsedLocations[3].includes(parsedLocations[0]));
		assertFalse(parsedLocations[4].includes(parsedLocations[0]));
	}
	
	@Test
	public void testContains2() {
		Location outer = Location.parseLocation("line 109, col 1 to line 120, col 19 of module EWD998Chan");
		Location inner = Location.parseLocation("line 119, col 24 to line 119, col 28 of module EWD998Chan");
		assertFalse(inner.includes(outer));
		assertTrue(outer.includes(inner));
		
		outer = Location.parseLocation("line 6, col 1 to line 6, col 16 of module Debug02");
		inner = Location.parseLocation("line 6, col 9 to line 6, col 9 of module Debug02");
		assertFalse(inner.includes(outer));
		assertTrue(outer.includes(inner));
	}
	
	@Test
	public void testComparator() {
		final Location[] parsedLocations = Location.getParsedLocations(
				  "line 15, col 9 to line 15, col 9 of module CostMetrics\n"
				+ "line 15, col 9 to line 15, col 17 of module CostMetrics\n"
				+ "line 8, col 11 to line 8, col 11 of module CostMetrics\n"
				+ "line 8, col 13 to line 8, col 13 of module CostMetrics\n"
				+ "line 8, col 9 to line 8, col 15 of module CostMetrics\n"
				+ "line 14, col 15 to line 14, col 17 of module CostMetrics\n"
				+ "line 15, col 15 to line 15, col 17 of module CostMetrics\n"
				+ "line 16, col 34 to line 16, col 52 of module CostMetrics\n"
				+ "line 8, col 9 to line 8, col 15 of module CostMetrics\n"
				+ "line 16, col 42 to line 16, col 51 of module CostMetrics\n"
				+ "line 16, col 42 to line 16, col 50 of module CostMetrics\n"
				+ "line 16, col 46 to line 16, col 46 of module CostMetrics\n"
				+ "line 16, col 46 to line 16, col 50 of module CostMetrics\n"
				+ "line 16, col 46 to line 16, col 50 of module CostMetrics\n"
				+ "line 23, col 6 to line 25, col 18 of module CostMetrics\n"
				+ "line 18, col 9 to line 18, col 9 of module CostMetrics");
		assertEquals(16, parsedLocations.length);
		
		final TreeSet<Location> locations = new TreeSet<>(Arrays.asList(parsedLocations));
		assertEquals(14, locations.size());
		
		final Iterator<Location> iterator = locations.iterator();
		Location l = iterator.next();
		for (int i = 1; i < locations.size(); i++) {
			final Location next = iterator.next();
			assertTrue(l.bLine <= next.bLine);
			if (l.bLine == next.bLine) {
				assertTrue(l.bColumn <= next.bColumn);
				if (l.bColumn == next.bColumn) {
					assertTrue(l.eLine <= next.eLine);
					if (l.eLine == next.eLine) {
						assertTrue(l.eColumn < next.eColumn);
					}
				}
			}
			l = next;
		}
	}
}
