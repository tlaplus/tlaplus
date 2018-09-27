package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class CoverageInformation implements Iterable<CoverageInformationItem> {
	
	private long maxValue = -1l;
	
	private final List<CoverageInformationItem> items = new ArrayList<>();

	public void add(CoverageInformationItem item) {
		this.maxValue = Math.max(this.maxValue, item.getCount());
		this.items.add(item);
	}

	@Override
	public Iterator<CoverageInformationItem> iterator() {
		return this.items.iterator();
	}

	public boolean isEmpty() {
		return this.items.isEmpty();
	}

	public long getMaxCount() {
		return maxValue;
	}

	public Object[] toArray() {
		return this.items.toArray();
	}
}
