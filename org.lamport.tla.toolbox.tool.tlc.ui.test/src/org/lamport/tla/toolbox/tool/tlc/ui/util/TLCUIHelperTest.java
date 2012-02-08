// Copyright (c) Feb 6, 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.List;

import junit.framework.Assert;

import org.eclipse.swt.custom.StyleRange;
import org.junit.Test;

import tla2sany.st.Location;

/**
 * @author Markus Alexander Kuppe
 */
public class TLCUIHelperTest {

	private final String module = "RemoveRedundantParens";
	private final int line = 1;
	private final int beginColumn = 1;
	private final int endColumn = 2;

	@Test
	public void testSetTLCLocationHyperlinksString() {
		final String text = 
				  "0. Line " + line + ", column " + beginColumn + " to line " + line + ", column " + endColumn + " in " + module + "\n"
				+ "4. Line " + line + ", column " + beginColumn + " to line " + line + ", column " + endColumn + " in " + module;

		final List<StyleRange> ranges = TLCUIHelper.setTLCLocationHyperlinks(text);

		// check if we get expected amount of locations
		Assert.assertEquals(2, ranges.size());
		
		// check each location individually
		for (final StyleRange range : ranges) {
			if (range.data instanceof Location) {
				final Location location = (Location) range.data;
				Assert.assertEquals(module, location.source());
				Assert.assertEquals(line, location.beginLine());
				Assert.assertEquals(line, location.endLine());
				Assert.assertEquals(beginColumn, location.beginColumn());
				Assert.assertEquals(endColumn, location.endColumn());
			}
		}
	}
	
	@Test
	public void testTLAandPCalLocations() {
		final String text =
				// PCal
				"Failure of assertion at line " + line	+ ", column " + beginColumn + ".\n" +
				// TLA
				"4. Line " + line+ ", column " + beginColumn + " to line " + line + ", column "	+ endColumn + " in " + module;

		final List<StyleRange> ranges = TLCUIHelper.setTLCLocationHyperlinks(text);

		// check if we get expected amount of locations
		Assert.assertEquals(2, ranges.size());
		
		// check each location individually
		for (final StyleRange range : ranges) {
			if (range.data instanceof Location) {
				final Location location = (Location) range.data;
				Assert.assertEquals(module, location.source());
				Assert.assertEquals(line, location.beginLine());
				Assert.assertEquals(beginColumn, location.beginColumn());
				// ignore end line and endColumn here as the PCal matcher does
				// not know and hence set this information.
			}
		}
	}
}
