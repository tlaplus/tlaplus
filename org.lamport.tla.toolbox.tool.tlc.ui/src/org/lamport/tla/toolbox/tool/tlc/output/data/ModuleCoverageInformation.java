/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.graphics.RGB;
import org.lamport.tla.toolbox.tool.tlc.output.data.Representation.Grouping;

import tla2sany.st.Location;

public class ModuleCoverageInformation {
	
	public static final String GRAY = "GRAY";

	public static final String RED = "RED";
	
	static {
		JFaceResources.getColorRegistry().put(RED, new RGB(255,0,0));
		JFaceResources.getColorRegistry().put(GRAY, new RGB(211,211,211));
	}

	private static final int BLUE = 240;

	static int getHue(final long count, final TreeSet<Long> counts) {
		final int size = counts.size();
		final float r = 240f / size;
		final SortedSet<Long> headSet = counts.headSet(count);
		return BLUE - Math.round(r * (headSet.size() + 1));
	}

	private static CoverageInformationItem getRoot(final List<CoverageInformationItem> items, final IFile file) {
		// Root is the technical root acting as entry point for the editor. It doesn't
		// have a location or counts. Its only children are ActionInformationItems.
		final CoverageInformationItem root = new RootCoverageInformationItem();
		
		final Deque<CoverageInformationItem> stack = new ArrayDeque<>();
		stack.push(root);
		
		// AII is the (logical) root of the current CostModel. It has a location and
		// counts.
		ActionInformationItem aiiRoot = null;
		for (CoverageInformationItem item : items) {
			if (item.isInFile(file)) {
				if (item instanceof ActionInformationItem) {
					aiiRoot = (ActionInformationItem) item;
				}
				int layer = item.getLayer();
				while (layer <= stack.peek().getLayer()) {
					stack.pop();
				}
				stack.peek().addChild(item);
				stack.push(item);
			} else if (aiiRoot == null && item instanceof ActionInformationItem) {
				// aiiroot is in a different file, e.g. definition of Init or Next in MC.tla.
				aiiRoot = new ActionInformationItem((ActionInformationItem) item);
				aiiRoot.setIsNotInFile();
				root.addChild(aiiRoot);
				stack.push(aiiRoot);
			}
		}
		assert root.getChildren().stream().allMatch(c -> c instanceof ActionInformationItem);
		
		return root;
	}

	//-------------------------//
	
	private final Map<Location, List<CoverageInformationItem>> loc2cci = new HashMap<>();
	
	private final TreeMap<Integer, List<CoverageInformationItem>> offset2cii = new TreeMap<>();
	
	private final Map<Representation, TreeSet<CoverageInformationItem>> rootLegends = new HashMap<>();

	private final IFile file;

	private final List<CoverageInformationItem> allItems;

	private CoverageInformationItem root;

	public ModuleCoverageInformation(final IFile file, final List<CoverageInformationItem> allItems) {
		this.file = file;
		this.allItems = allItems;
		
		// The subset of items that belong to this file.
		final List<CoverageInformationItem> subset = allItems.stream().filter(i -> i.isInFile(file))
				.collect(Collectors.toList());

		// Group items belonging to the same location/region.
		for (CoverageInformationItem item : subset) {
			this.loc2cci.computeIfAbsent(item.getModuleLocation(), c -> new ArrayList<>()).add(item);
			this.offset2cii.computeIfAbsent(item.getRegion().getOffset(), c -> new ArrayList<>()).add(item);
		}
		for (CoverageInformationItem item : subset) {
			// Set siblings if any:
			item.setSiblings(loc2cci.get(item.getModuleLocation()));
		}
		
		// Initialize legends for each representation.
		for (Representation rep : Representation.values()) {
			this.rootLegends.put(rep, new TreeSet<CoverageInformationItem>(rep.getComparator(Grouping.COMBINED)));
		}
		
		// Calculate the range of values for the ActionInformationItems.
		final List<ActionInformationItem> actionSubset = subset.stream()
				.filter(cii -> cii instanceof ActionInformationItem).map(ActionInformationItem.class::cast)
				.collect(Collectors.toList());
		
		// Sum of all distinct states.
		final long sum = actionSubset.stream().mapToLong(ActionInformationItem::getUnseen).sum();

		final TreeSet<Long> distinctStateCounts = new TreeSet<>();
		final TreeSet<Long> stateCounts = new TreeSet<>();
		actionSubset.forEach(a -> {
			distinctStateCounts.add(a.getUnseen());
			stateCounts.add(a.getCount());
			a.setSum(sum);
		});
		// With aiiCounts collected, update all actions.
		actionSubset.forEach(a -> {
			a.colorItem(distinctStateCounts, stateCounts);
			rootLegends.get(Representation.STATES).add(a);
			rootLegends.get(Representation.STATES_DISTINCT).add(a);
		});
		
		final List<Representation> values = Arrays.asList(Representation.values()).stream()
				.filter(rep -> rep != Representation.STATES && rep != Representation.STATES_DISTINCT)
				.collect(Collectors.toList());

		// Style the CIIs for each representation.
		subset.removeAll(actionSubset);
		for (Representation rep : values) {
			final TreeSet<Long> ciiCounts = new TreeSet<>();
			
			for (final CoverageInformationItem item : subset) {
				ciiCounts.add(rep.getValue(item, Grouping.INDIVIDUAL));
				ciiCounts.add(rep.getValue(item, Grouping.COMBINED));
			}
			// Color each item according to the previously calculated ranges.
			final Set<CoverageInformationItem> set = rootLegends.get(rep);
			for (final CoverageInformationItem item : subset) {
				// Calculate colors for CII.
				item.colorItem(ciiCounts, rep);
				
				set.add(item);
			}
		}
	}
	
	// false if a module has no actions (e.g. standard modules).
	public boolean hasStates() {
		return this.allItems.stream().filter(i -> i.isInFile(this.file) && i instanceof ActionInformationItem)
				.count() > 0L;
	}

	public CoverageInformationItem getRoot() {
		if (this.root == null) {
			// Create the tree out of the flat list of items (the tree might span multiple
			// files which is why we pass allItems). getRoot is expected to be called
			// outside the UI thread.
			this.root = getRoot(allItems, file);
		}
		return root;
	}
	
	private List<CoverageInformationItem> getNodes(final int offset) {
		final Entry<Integer, List<CoverageInformationItem>> entry = this.offset2cii.floorEntry(offset);
		if (entry != null) {
			return entry.getValue().stream()
					.filter(cii -> offset <= cii.getRegion().getOffset() + cii.getRegion().getLength())
					.collect(Collectors.toList());
		}
		return new ArrayList<>();
	}
	
	public CoverageInformationItem getNode(final int offset) {
		return getNodes(offset).stream().findFirst().orElse(null);
	}

	public String getHoverInfo(final int offset) {
		final List<CoverageInformationItem> nodes = getNodes(offset);
		
		final List<CoverageInformationItem> sorted = nodes.stream()
				.filter(cii -> !(cii instanceof ActionInformationItem))
				.sorted((c1, c2) -> c1.isActive() ? -1 : c2.isActive() ? 1 : Long.compare(c1.getCount(), c2.getCount()))
				.collect(Collectors.toList());
		
		String hover = "", plus = "";
		Long sum = 0L;
		for (CoverageInformationItem cii : sorted) {
			final long count = cii.getCount();
			sum += count;
			String cost = "";
			if (cii.getCost() > 0) {
				cost = String.format(", cost %s", cii.getCost());
			}
			hover = String.format("%s%s%,d invocation%s%s (%s)\n", hover, plus, count, count == 1 ? "" : "s", cost,
					cii.getRoot().getLocation());
			plus = "+";
		}

		if (sorted.size() > 1 && sum > 0) {
			hover += String.format("---------\n%,d invocations", sum);
		}
		
		
		final List<CoverageInformationItem> actionItems = nodes.stream().filter(cii -> cii instanceof ActionInformationItem)
				.collect(Collectors.toList());
		if (!actionItems.isEmpty()) {
			hover += "\n";
			for (CoverageInformationItem cii : actionItems) {
				final ActionInformationItem aii = (ActionInformationItem) cii;
				hover += aii.getHover();
				hover += "\n";
			}
		}
		
		return hover.replaceAll("^\n", "").replaceAll("\n$", "");
	}

	public TreeSet<CoverageInformationItem> getLegend(final Representation rep) {
		return rootLegends.get(rep);
	}
}
