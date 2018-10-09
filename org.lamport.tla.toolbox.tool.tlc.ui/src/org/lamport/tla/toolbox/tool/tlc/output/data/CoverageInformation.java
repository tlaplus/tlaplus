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
package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

public class CoverageInformation implements Iterable<CoverageInformationItem> {
	
	private final TreeSet<Long> counts = new TreeSet<>();
	
	private final List<CoverageInformationItem> items = new ArrayList<>();

	public void add(final CoverageInformationItem item) {
		this.counts.add(item.getCount());
		this.items.add(item);
	}

	@Override
	public Iterator<CoverageInformationItem> iterator() {
		return this.items.iterator();
	}

	public boolean isEmpty() {
		return this.items.isEmpty();
	}

	public Object[] toArray() {
		return this.items.toArray();
	}

	private static final int BLUE = 240;

	public int getHue(final CoverageInformationItem item) {
		final int size = counts.size();
		final float r = 240f / size;
		final SortedSet<Long> headSet = counts.headSet(item.getCount());
		return BLUE - Math.round(r * headSet.size());
	}
}
