// Copyright (c) Dec 12, 2011 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.tool.tlc.output.data;

import junit.framework.TestCase;

/**
 * @author Markus Alexander Kuppe
 */
public class StateSpaceInformationItemTest extends TestCase {

	/*
	 * (non-Javadoc)
	 * 
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
	}

	/**
	 * Test method for
	 * {@link org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem#parse(java.lang.String)}
	 * .
	 */
	public void testParse() {
		String outputMessage = "Progress(10) at 2011-12-12 17:16:45: 36114 states generated (658832 s/min)," +
				" 9392 distinct states found (9127 ds/min), 4232 states left on queue. is in wrong format";
		StateSpaceInformationItem parsed = StateSpaceInformationItem
				.parse(outputMessage);
		assertEquals(10, parsed.getDiameter());
		assertEquals(9392, parsed.getDistinctStates());
		assertEquals(36114, parsed.getFoundStates());
		assertEquals(4232, parsed.getLeftStates());
		assertEquals(658832, parsed.getSpm());
		assertEquals(9127, parsed.getDistinctSPM());
	}

}
