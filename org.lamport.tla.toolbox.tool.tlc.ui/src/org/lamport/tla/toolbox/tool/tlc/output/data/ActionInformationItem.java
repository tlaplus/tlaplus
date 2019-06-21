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

import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

import tla2sany.st.Location;
import tlc2.tool.coverage.ActionWrapper.Relation;

public class ActionInformationItem extends CoverageInformationItem {

	private static final Pattern pattern = Pattern.compile("^<(.*?) (line [^(]+)( \\(([0-9 ]+)\\))?>: ([0-9]+):([0-9]+)$");
	
	public static final int actionLayer = RootCoverageInformationItem.rootLayer + 1;
	
	public static ActionInformationItem parseInit(String outputMessage, String modelName) {
		return parseInitAndNext(Relation.INIT, outputMessage, modelName);
	}

	public static ActionInformationItem parseNext(String outputMessage, String modelName) {
		return parseInitAndNext(Relation.NEXT, outputMessage, modelName);
	}

	private static ActionInformationItem parseInitAndNext(Relation rel, String outputMessage, String modelName) {
		final Matcher matcher = pattern.matcher(outputMessage);
		matcher.find();
		
		final Location declaration = Location.parseLocation(matcher.group(2));
		
		// Optional group with the definition.
		final String group4 = matcher.group(4);
		Location definition = null;
		if (group4 != null) {
			definition = Location.parseCoordinates(declaration.source(), group4);
		}
		
		final long distinctStates = Long.parseLong(matcher.group(5));
		final long generatedStates = Long.parseLong(matcher.group(6));
		
		return new ActionInformationItem(rel, matcher.group(1), declaration, definition, modelName,
				generatedStates, distinctStates);
	}
	
	
	public static ActionInformationItem parseProp(String outputMessage, String modelName) {
		final Pattern pattern = Pattern.compile("^<(.*?) (line .*)>$");
		final Matcher matcher = pattern.matcher(outputMessage);
		matcher.find();

		final Location location = Location.parseLocation(matcher.group(2));
		
		return new ActionInformationItem(matcher.group(1), location, modelName);
	}
	
	// ---- ---- //
	
	private final Relation relation;
	private final String name;
	private long sum;
	private boolean isNotInFile = false;

	/**
	 * @see tlc2.tool.coverage.ActionWrapper.printLocation()
	 */
	private final Location definition;

	public ActionInformationItem(final String name, Location loc, final String modelName) {
		super(loc, 0, modelName, actionLayer);
		this.name = name;
		this.relation = Relation.PROP;
		this.definition = null;
	}
	
	public ActionInformationItem(final Relation relation, final String name, Location loc, Location definition,
			final String modelName, long generated, long unseen) {
		super(loc, generated, unseen, modelName, actionLayer);
		this.name = name;
		this.relation = relation;
		this.definition = definition;
	}

	ActionInformationItem(ActionInformationItem item) {
		super(item.location, item.count, item.cost, item.modelName, item.layer);
		this.name = item.name;
		this.relation = item.relation;
		this.definition = item.definition;
	}

	public String getName() {
		return name;
	}
	
	public Relation getRelation() {
		return relation;
	}
	
	/**
	 * @return a Location or null if the definition location is unknown
	 * @see tlc2.tool.coverage.ActionWrapper.printLocation()
	 */
	public Location getDefinition() {
		return definition;
	}

	public boolean hasDefinition() {
		return definition != null;
	}

	@Override
    public boolean includeInCounts() {
		if (relation == Relation.PROP && count == 0) {
			// Count should always be zero but better be safe than sorry. The reason to
			// exclude PROP from counts is to prevent bogus zero coverage reports for
			// properties. Consider the spec below:
			// ---- Foo ----
			// VARIABLE x
			// Init == ...
			// Next == ...
			// TypeOK == x \in Nat
			// =====
			// The ActionInformationItem instance for the expression "TypeOK" (just the
			// left-hand side), has zero count. The right-hand side will however report
			// its count.
			return false;
		}
    	return true;
    }

	/**
	 * Number of *distinct* states.
	 */
	public long getUnseen() {
		return getCost();
	}
	
	public CoverageInformationItem setIsNotInFile() {
		this.isNotInFile = true;
		return this;
	}
	
	@Override
	CoverageInformationItem addChild(CoverageInformationItem child) {
		super.addChild(child);
		
		assert child.getRoot() == null;
		child.setRoot(this); // overwrite root set by super.addChild
		return this;
	}

	@Override
	protected StyleRange addStlye(final StyleRange sr) {
		sr.borderStyle = SWT.BORDER_DOT;
		return sr;
	}
	
	@Override
	public void style(TextPresentation textPresentation, final Representation rep) {
		if (relation == Relation.PROP) {
			return;
		} else if (isNotInFile) {
			// Skip styling this item but style its children.
			for (CoverageInformationItem child : getChildren()) {
				child.style(textPresentation, rep);
			}
			return;
		}
		super.style(textPresentation, rep);
	}
	
	@Override
	protected void style(final TextPresentation textPresentation, boolean merge, final Representation rep) {
		if (relation == Relation.PROP) {
			return;
		} else if (isNotInFile) {
			// Skip styling this item but style its children.
			for (CoverageInformationItem child : getChildren()) {
				child.style(textPresentation, merge, rep);
			}
			return;
		}
		super.style(textPresentation, merge, rep);
	}

	@Override
	public void style(final TextPresentation textPresentation, final Color c, final Representation rep) {
		// Do not unstyle AII when specific CostModel tree gets selected.
		for (CoverageInformationItem child : getChildren()) {
			child.style(textPresentation, c, rep);
		}
	}

	@Override
	Color colorItem(TreeSet<Long> counts, final Representation ignored) {
		// This shouldn't be called because the second parameter is bogus. I don't think
		// it is called but decided to better leave it in.
		return colorItem(counts, counts);
	}

	Color colorItem(final TreeSet<Long> distinctStateCounts, final TreeSet<Long> stateCounts) {
		// Distinct states colors...
		for (Representation rep : Representation.values()) {
			// Always use the same representation (also for the unrelated representations
			// Inv, Cost, InvCost to avoid NPEs).
			representations.put(rep, createColors(distinctStateCounts, getUnseen()));
		}
		
		// For non-distinct states calculate a dedicated color mapping and replace the
		// incorrect color mapping from the previous for loop with the correct one.
		representations.put(Representation.STATES, createColors(stateCounts, getCount()));
		
		// Return one of the colors (should be ignored anyway).
		return representations.get(Representation.STATES)[0];
	}

	private Color[] createColors(final TreeSet<Long> counts, long count) {
		final int hue = ModuleCoverageInformation.getHue(count, counts);
		final String key = Integer.toString(hue);
		if (!JFaceResources.getColorRegistry().hasValueFor(key)) {
			JFaceResources.getColorRegistry().put(key, new RGB(hue, .25f, 1f));
		}
		return new Color[] { JFaceResources.getColorRegistry().get(key), JFaceResources.getColorRegistry().get(key) };
	}

	public String getHover() {
		final String definition = hasDefinition() ? " (" + getDefinition().linesAndColumns() + ")" : "";
		if (relation == Relation.PROP){
			return "";
		} else if (relation == Relation.NEXT) {
			if (getCount() == 0) {
				return String.format("Action %s%s:\n- No states found\n", name, definition);
			} else if (getUnseen() == 0) {
				return String.format("Action %s%s:\n- %,d state%s found but none distinct\n", name, definition, getCount(),
						getCount() == 1 ? "" : "s");
			} else {
				final double ratio = (getUnseen() * 1d / sum) * 100d;
				final double overhead = (getUnseen() * 1d / getCount()) * 100d;
				return String.format(
						"Action %s%s:\n- %,d state%s found with %,d distinct (%.2f%%)\n- Contributes %.2f%% to total number of distinct states across all actions\n",
						name, definition, getCount(), getCount() == 1 ? "" : "s", getUnseen(), overhead, ratio);
			}
		} else if (relation == Relation.INIT) {
			return String.format("Action %s%s (Init):\n- %,d state%s found", name, definition, getCount(),
					getCount() == 1 ? "" : "s");
		}
		return "";
	}

	public void setSum(final long sum) {
		this.sum = sum;
	}
}
