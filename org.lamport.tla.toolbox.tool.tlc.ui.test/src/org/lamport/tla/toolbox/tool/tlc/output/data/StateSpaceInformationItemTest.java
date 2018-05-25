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
	
	/**
	 * Test method for
	 * {@link org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem#parseInit(java.lang.String)}
	 * .
	 */
	public void testParseInit() {
		StateSpaceInformationItem parsed = StateSpaceInformationItem
				.parseInit("Finished computing initial states: 123456789 distinct states generated.");
		assertEquals(0, parsed.getDiameter());
		assertEquals(123456789, parsed.getDistinctStates());
		assertEquals(123456789, parsed.getFoundStates());
		assertEquals(123456789, parsed.getLeftStates());
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}
	
	public void testParseInit2() {
		StateSpaceInformationItem parsed = StateSpaceInformationItem
				.parseInit("Finished computing initial states: 1 distinct state generated.");
		assertEquals(0, parsed.getDiameter());
		assertEquals(1, parsed.getDistinctStates());
		assertEquals(1, parsed.getFoundStates());
		assertEquals(1, parsed.getLeftStates());
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}

	public void testParseInit3() {
		StateSpaceInformationItem parsed = StateSpaceInformationItem
				.parseInit("Finished computing initial states: 123456789 states generated, with 123 of them distinct.");
		assertEquals(0, parsed.getDiameter());
		assertEquals(123, parsed.getDistinctStates());
		assertEquals(123456789, parsed.getFoundStates());
		assertEquals(123, parsed.getLeftStates());
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}

	public void testParseInit4() {
		StateSpaceInformationItem parsed = StateSpaceInformationItem
				.parseInit("Finished computing initial states: 2 states generated, with 1 of them distinct.");
		assertEquals(0, parsed.getDiameter());
		assertEquals(1, parsed.getDistinctStates());
		assertEquals(2, parsed.getFoundStates());
		assertEquals(1, parsed.getLeftStates());
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}
}
