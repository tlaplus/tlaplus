// Copyright (c) Dec 12, 2011 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.text.ParseException;
import java.text.SimpleDateFormat;

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

	public void testParseInit5() throws ParseException {
		StateSpaceInformationItem parsed = StateSpaceInformationItem
				.parseInit("Finished computing initial states: 2 distinct states generated at 2018-07-03 16:10:44.");

		assertEquals(new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").parse("2018-07-03 16:10:44"), parsed.getTime());
		assertEquals(0, parsed.getDiameter());
		assertEquals(2, parsed.getDistinctStates());
		assertEquals(2, parsed.getFoundStates());
		assertEquals(2, parsed.getLeftStates());
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}

	public void testParseInit6() throws ParseException {
		StateSpaceInformationItem parsed = StateSpaceInformationItem.parseInit(
				"Finished computing initial states: 2 states generated, with 1 of them distinct at 2018-07-03 16:10:44.");

		assertEquals(new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").parse("2018-07-03 16:10:44"), parsed.getTime());
		assertEquals(0, parsed.getDiameter());
		assertEquals(1, parsed.getDistinctStates());
		assertEquals(2, parsed.getFoundStates());
		assertEquals(1, parsed.getLeftStates());
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}
	
	public void testParseOldComma() throws ParseException {
		StateSpaceInformationItem parsed = StateSpaceInformationItem.parseOld(
				"Progress(57) at 2019-03-21 10:20:20: 48,613 states generated, 25,188 distinct states found, 556,000 states left on queue.");
		
		assertEquals(57, parsed.getDiameter());
		assertEquals(48613, parsed.getFoundStates());
		assertEquals(25188, parsed.getDistinctStates());
		assertEquals(556000, parsed.getLeftStates());
		
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}
	
	public void testParseOldDot() throws ParseException {
		StateSpaceInformationItem parsed = StateSpaceInformationItem.parseOld(
				"Progress(57) at 2019-03-21 10:20:20: 48.613 states generated, 25.188 distinct states found, 556.000 states left on queue.");
		
		assertEquals(57, parsed.getDiameter());
		assertEquals(48613, parsed.getFoundStates());
		assertEquals(25188, parsed.getDistinctStates());
		assertEquals(556000, parsed.getLeftStates());
		
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}
	
	public void testParseOld() throws ParseException {
		StateSpaceInformationItem parsed = StateSpaceInformationItem.parseOld(
				"Progress(57) at 2019-03-21 10:20:20: 48613 states generated, 25188 distinct states found, 556000 states left on queue.");
		
		assertEquals(57, parsed.getDiameter());
		assertEquals(48613, parsed.getFoundStates());
		assertEquals(25188, parsed.getDistinctStates());
		assertEquals(556000, parsed.getLeftStates());
		
		assertEquals(0, parsed.getSpm());
		assertEquals(0, parsed.getDistinctSPM());
	}
}
