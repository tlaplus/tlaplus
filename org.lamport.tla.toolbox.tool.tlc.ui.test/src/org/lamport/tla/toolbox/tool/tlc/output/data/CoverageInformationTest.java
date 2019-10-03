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

import static org.junit.Assert.assertTrue;
import static org.lamport.tla.toolbox.tool.tlc.output.data.Representation.*;
import static org.lamport.tla.toolbox.tool.tlc.output.data.Representation.Grouping.*;

import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.TreeSet;
import java.util.function.Function;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.text.TextPresentation;
import org.junit.BeforeClass;
import org.junit.Test;
import org.lamport.tla.toolbox.tool.tlc.output.data.Representation.Grouping;

public class CoverageInformationTest {

	private static ModuleCoverageInformation mci;

	@BeforeClass
	public static void setup() throws IOException, CoreException {
		// Create an IFile instance (this is a witness of why the Eclipse Resource API
		// is probably one of the worst APIs ever with the exception of those that I've
		// written).
		final String name = "CoverageInformationTestProject";
		final IProjectDescription desc = ResourcesPlugin.getWorkspace().newProjectDescription(name);
		final IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(name);
		project.create(desc, new NullProgressMonitor());
		project.open(new NullProgressMonitor());
		final IFile file = project.getFile("Simple.tla");
		final InputStream source = CoverageInformationTest.class.getResourceAsStream("Simple.tla");
		file.create(source, IFile.FORCE, null);

		final CoverageInformation ci = new CoverageInformation(Arrays.asList(new IFile[] { file }));

		ci.add(ActionInformationItem.parseInit("<Init line 28, col 1 to line 28, col 4 of module Simple>: 3:3", "M"));
		ci.add(CoverageInformationItem.parse("line 29, col 12 to line 29, col 35 of module Simple: 1", "M"));
		ci.add(CoverageInformationItem.parse("line 30, col 12 to line 30, col 35 of module Simple: 1", "M"));
		ci.add(CoverageInformationItem.parse("line 31, col 12 to line 31, col 21 of module Simple: 1", "M"));
		ci.add(CoverageInformationItem.parse("line 32, col 12 to line 32, col 42 of module Simple: 3", "M"));

		ci.add(ActionInformationItem.parseNext("<a line 34, col 1 to line 34, col 7 of module Simple>: 63:99", "M"));
		ci.add(CoverageInformationItem.parse("line 34, col 15 to line 34, col 28 of module Simple: 558", "M"));
		ci.add(CoverageInformationItem.parse("|line 34, col 15 to line 34, col 22 of module Simple: 459", "M"));
		ci.add(CoverageInformationItem.parse("line 35, col 15 to line 35, col 41 of module Simple: 99", "M"));
		ci.add(CoverageInformationItem.parse("line 36, col 15 to line 36, col 45 of module Simple: 99", "M"));
		ci.add(CoverageInformationItem.parse("line 37, col 15 to line 37, col 30 of module Simple: 99", "M"));
		ci.add(CoverageInformationItem.parse("line 38, col 15 to line 38, col 27 of module Simple: 99", "M"));
		ci.add(CoverageInformationItem.parse("|line 7, col 15 to line 7, col 65 of module Simple: 99", "M"));
		ci.add(CoverageInformationItem.parse("||line 7, col 35 to line 7, col 65 of module Simple: 792", "M"));
		ci.add(CoverageInformationItem.parse("|||line 7, col 35 to line 7, col 41 of module Simple: 792", "M"));
		ci.add(CoverageInformationItem.parse("|||line 7, col 46 to line 7, col 65 of module Simple: 693", "M"));
		ci.add(CoverageInformationItem.parse("||||line 7, col 59 to line 7, col 65 of module Simple: 1188", "M"));
		ci.add(CoverageInformationItem.parse("||||line 7, col 55 to line 7, col 56 of module Simple: 693", "M"));
		ci.add(CoverageInformationItem.parseCost("||line 7, col 25 to line 7, col 32 of module Simple: 99:1881", "M"));
		ci.add(CoverageInformationItem.parse("|line 38, col 23 to line 38, col 26 of module Simple: 99", "M"));

		ci.add(ActionInformationItem.parseNext("<b line 40, col 1 to line 40, col 7 of module Simple>: 87:261", "M"));
		ci.add(CoverageInformationItem.parse("line 40, col 15 to line 40, col 25 of module Simple: 720", "M"));
		ci.add(CoverageInformationItem.parse("|line 40, col 15 to line 40, col 21 of module Simple: 459", "M"));
		ci.add(CoverageInformationItem.parse("line 40, col 30 to line 40, col 40 of module Simple: 621", "M"));
		ci.add(CoverageInformationItem.parse("|line 40, col 30 to line 40, col 36 of module Simple: 360", "M"));
		ci.add(CoverageInformationItem.parse("line 41, col 15 to line 41, col 55 of module Simple: 261", "M"));
		ci.add(CoverageInformationItem.parse("line 42, col 15 to line 42, col 48 of module Simple: 261", "M"));
		ci.add(CoverageInformationItem.parse("line 43, col 15 to line 43, col 30 of module Simple: 261", "M"));
		ci.add(CoverageInformationItem.parse("line 44, col 15 to line 44, col 27 of module Simple: 261", "M"));
		ci.add(CoverageInformationItem.parse("|line 7, col 15 to line 7, col 65 of module Simple: 261", "M"));
		ci.add(CoverageInformationItem.parse("||line 7, col 35 to line 7, col 65 of module Simple: 8352", "M"));
		ci.add(CoverageInformationItem.parse("|||line 7, col 35 to line 7, col 41 of module Simple: 8352", "M"));
		ci.add(CoverageInformationItem.parse("|||line 7, col 46 to line 7, col 65 of module Simple: 8091", "M"));
		ci.add(CoverageInformationItem.parse("||||line 7, col 59 to line 7, col 65 of module Simple: 20880", "M"));
		ci.add(CoverageInformationItem.parse("||||line 7, col 55 to line 7, col 56 of module Simple: 8091", "M"));
		ci.add(CoverageInformationItem.parseCost("||line 7, col 25 to line 7, col 32 of module Simple: 261:28971",
				"M"));
		ci.add(CoverageInformationItem.parse("|line 44, col 23 to line 44, col 26 of module Simple: 261", "M"));

		ci.add(ActionInformationItem.parseNext("<Terminating line 49, col 1 to line 49, col 11 of module Simple>: 0:21",
				"M"));
		ci.add(CoverageInformationItem.parse("line 49, col 40 to line 49, col 56 of module Simple: 330", "M"));
		ci.add(CoverageInformationItem.parse("|line 49, col 40 to line 49, col 47 of module Simple: 267", "M"));
		ci.add(CoverageInformationItem.parse("line 49, col 31 to line 49, col 37 of module Simple: 153", "M"));
		ci.add(CoverageInformationItem.parse("line 50, col 19 to line 50, col 32 of module Simple: 21", "M"));

		mci = ci.projectionFor(file);
		mci.getRoot(); // initialize AII to CII parent-child relationship.
	}

	private static void monotonicallyIncreasing(TreeSet<CoverageInformationItem> set, Representation rep, Grouping grp,
			Function<CoverageInformationItem, Long> f) {
		long value = -1L;
		float hue = 240f;
		for (final CoverageInformationItem cii : set) {
			assertTrue(rep.getValue(cii, grp) == f.apply(cii));
			assertTrue(value <= f.apply(cii));
			value = f.apply(cii);

			// hue inversely correlates (non-linear relationship) with value, ie. value goes
			// up and hue goes down (but hue's actual value dependents on the set of all
			// values).
			final float h = rep.getColor(cii, grp).getRGB().getHSB()[0];
			assertTrue(hue >= h);
			hue = h;
		}
		assertTrue("legend was empty", value >= 0L);
	}

	private TreeSet<CoverageInformationItem> getNode(final int offset, final Representation rep) {
		final CoverageInformationItem node = mci.getNode(offset);
		// Style implicitly activates the children of node which getLegend requires.
		node.style(new TextPresentation(), rep);
		return node.getLegend(rep);
	}

	@Test
	public void rootLegendStates() {
		monotonicallyIncreasing(mci.getLegend(STATES), STATES, COMBINED, CoverageInformationItem::getCount);
		monotonicallyIncreasing(mci.getLegend(STATES), STATES, COMBINED, CoverageInformationItem::getTotalCount);
	}

	@Test
	public void rootLegendDistinctStates() {
		monotonicallyIncreasing(mci.getLegend(STATES_DISTINCT), STATES_DISTINCT, COMBINED,
				CoverageInformationItem::getCost);
		monotonicallyIncreasing(mci.getLegend(STATES_DISTINCT), STATES_DISTINCT, COMBINED,
				CoverageInformationItem::getTotalCost);
	}

	@Test
	public void rootLegendInvocations() {
		monotonicallyIncreasing(mci.getLegend(INV), INV, COMBINED, CoverageInformationItem::getTotalCount);
	}

	@Test
	public void rootLegendCost() {
		monotonicallyIncreasing(mci.getLegend(COST), COST, COMBINED, CoverageInformationItem::getTotalCost);
	}

	@Test
	public void rootLegendInvCost() {
		monotonicallyIncreasing(mci.getLegend(INVCOST), INVCOST, COMBINED,
				CoverageInformationItem::getTotalCountAndCost);
	}

	// Init predicate
	private static final int init = 775;

	@Test
	public void initLegendInv() {
		monotonicallyIncreasing(getNode(init, INV), INV, CoverageInformationItem::getCount);
	}

	@Test
	public void initLegendInvCost() {
		monotonicallyIncreasing(getNode(init, COST), COST, CoverageInformationItem::getCost);
	}

	@Test
	public void initLegendCost() {
		monotonicallyIncreasing(getNode(init, INVCOST), INVCOST, CoverageInformationItem::getCountAndCost);
	}

	@Test
	public void initLegendStates() {
		monotonicallyIncreasing(getNode(init, STATES), STATES, CoverageInformationItem::getCount);
		monotonicallyIncreasing(getNode(init, STATES), STATES, CoverageInformationItem::getTotalCount);
	}

	@Test
	public void initLegendDistStates() {
		monotonicallyIncreasing(getNode(init, STATES_DISTINCT), STATES_DISTINCT, CoverageInformationItem::getCost);
		monotonicallyIncreasing(getNode(init, STATES_DISTINCT), STATES_DISTINCT, CoverageInformationItem::getTotalCost);
	}

	// sub-action a
	private static final int suba = 944;

	@Test
	public void aLegendInv() {
		monotonicallyIncreasing(getNode(suba, INV), INV, CoverageInformationItem::getCount);
	}

	@Test
	public void aLegendInvCost() {
		monotonicallyIncreasing(getNode(suba, COST), COST, CoverageInformationItem::getCost);
	}

	@Test
	public void aLegendCost() {
		monotonicallyIncreasing(getNode(suba, INVCOST), INVCOST, CoverageInformationItem::getCountAndCost);
	}

	@Test
	public void aLegendStates() {
		monotonicallyIncreasing(getNode(suba, STATES), STATES, CoverageInformationItem::getCount);
		monotonicallyIncreasing(getNode(suba, STATES), STATES, CoverageInformationItem::getTotalCount);
	}

	@Test
	public void aLegendDistStates() {
		monotonicallyIncreasing(getNode(suba, STATES_DISTINCT), STATES_DISTINCT, CoverageInformationItem::getCost);
		monotonicallyIncreasing(getNode(suba, STATES_DISTINCT), STATES_DISTINCT, CoverageInformationItem::getTotalCost);
	}

	// sub-action b
	private static final int subb = 1121;

	@Test
	public void bLegendInv() {
		monotonicallyIncreasing(getNode(subb, INV), INV, CoverageInformationItem::getCount);
	}

	@Test
	public void bLegendInvCost() {
		monotonicallyIncreasing(getNode(subb, COST), COST, CoverageInformationItem::getCost);
	}

	@Test
	public void bLegendCost() {
		monotonicallyIncreasing(getNode(subb, INVCOST), INVCOST, CoverageInformationItem::getCountAndCost);
	}

	@Test
	public void bLegendStates() {
		monotonicallyIncreasing(getNode(subb, STATES), STATES, CoverageInformationItem::getCount);
		monotonicallyIncreasing(getNode(subb, STATES), STATES, CoverageInformationItem::getTotalCount);
	}

	@Test
	public void bLegendDistStates() {
		monotonicallyIncreasing(getNode(subb, STATES_DISTINCT), STATES_DISTINCT, CoverageInformationItem::getCost);
		monotonicallyIncreasing(getNode(subb, STATES_DISTINCT), STATES_DISTINCT, CoverageInformationItem::getTotalCost);
	}

	// Termination
	private static final int term = 1447;

	@Test
	public void termLegendInv() {
		monotonicallyIncreasing(getNode(term, INV), INV, CoverageInformationItem::getCount);
	}

	@Test
	public void termLegendInvCost() {
		monotonicallyIncreasing(getNode(term, COST), COST, CoverageInformationItem::getCost);
	}

	@Test
	public void termLegendCost() {
		monotonicallyIncreasing(getNode(term, INVCOST), INVCOST, CoverageInformationItem::getCountAndCost);
	}

	@Test
	public void termLegendStates() {
		monotonicallyIncreasing(getNode(term, STATES), STATES, CoverageInformationItem::getCount);
		monotonicallyIncreasing(getNode(term, STATES), STATES, CoverageInformationItem::getTotalCount);
	}

	@Test
	public void termLegendDistStates() {
		monotonicallyIncreasing(getNode(term, STATES_DISTINCT), STATES_DISTINCT, CoverageInformationItem::getCost);
		monotonicallyIncreasing(getNode(term, STATES_DISTINCT), STATES_DISTINCT, CoverageInformationItem::getTotalCost);
	}

	private static void monotonicallyIncreasing(TreeSet<CoverageInformationItem> set, Representation rep,
			Function<CoverageInformationItem, Long> f) {
		monotonicallyIncreasing(set, rep, INDIVIDUAL, f);
	}
}
