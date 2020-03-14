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

import static org.junit.Assert.*;

import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;

import org.junit.Test;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError.Order;

import tlc2.model.Formula;
import tlc2.model.TraceExpressionInformationHolder;
import util.TLAConstants;

public class TLCErrorTest {
	
	@Test
	public void testA() {
		test(Order.OneToN, Order.NToOne, 0, 1);
	}
	@Test
	public void testB() {
		test(Order.NToOne, Order.OneToN, 1, 0);
	}
	@Test
	public void testC() {
		test(Order.OneToN, Order.OneToN, 0, 1);
	}
	@Test
	public void testD() {
		test(Order.NToOne, Order.NToOne, 1, 0);
	}
	
	private static void test(final Order sortMC, final Order sortTE, final int init, final int next) {
		final String modelName = "Model_1";
		final Map<String, Formula> traceExplorerExpressions = new HashMap<String, Formula>();
		final Hashtable<String, TraceExpressionInformationHolder> traceExpressionDataTable = getTraceExpressionDataTable();
		
		// error origination for a "regular" TLC run.
		final TLCError mcError = new TLCError(sortMC);
		final TLCState mcInitState = TLCState.parseState("1: <Initial predicate>\n" + 
				"/\\ store = <<>>\n" + 
				"/\\ waitC = {}\n" + 
				"/\\ waitP = {}", modelName);
		mcError.addState(mcInitState);
		final TLCState mcNextState = TLCState.parseState("2: <p2 line 63, col 13 to line 66, col 36 of module BlockingQueue>\n" + 
				"/\\ store = <<\"data\">>\n" + 
				"/\\ waitC = {}\n" + 
				"/\\ waitP = {}", modelName);
		mcError.addState(mcNextState);
		
		// error originating from a trace expression evaluation.
		final TLCError teError = new TLCError(sortTE);
		teError.addState(TLCState.parseState("1: <Initial predicate>\n" + 
				"/\\ store = <<>>\n" + 
				"/\\ waitC = {}\n" + 
				"/\\ waitP = {}\n" + 
				"/\\ __trace_var_155717784845014000 = 1\n" + 
				"/\\ __trace_var_155717784845012000 = TRUE", modelName));
		teError.addState(TLCState.parseState("2: <next_155717784845016000 line 44, col 3 to line 67, col 2 of module TE>\n" + 
				"/\\ store = <<\"data\">>\n" + 
				"/\\ waitC = {}\n" + 
				"/\\ waitP = {}\n" + 
				"/\\ __trace_var_155717784845014000 = 2\n" + 
				"/\\ __trace_var_155717784845012000 = FALSE", modelName));
		
		// Merge teError with mcError
		teError.applyFrom(mcError, traceExplorerExpressions, traceExpressionDataTable, modelName);
		
		final List<TLCState> teStates = teError.getStates();
		assertEquals(2, teStates.size());
		
		final TLCState teInitState = teStates.get(init);
		assertTrue(teInitState.isInitialState());
		assertEquals(mcInitState.getLabel(), teInitState.getLabel());
		assertEquals(mcInitState.getStateNumber(), teInitState.getStateNumber());
		assertEquals(mcInitState.getVariableCount(1) + 2, teInitState.getVariableCount(1));
		final Map<String, TLCVariable> teInitDiff = teInitState.getDiff(mcInitState);
		assertEquals(2, teInitDiff.size());
		assertEquals(teInitDiff.get(TLAConstants.TraceExplore.POSITION).toString(), "1");
		assertEquals(teInitDiff.get("store = <<>>").toString(), "TRUE");

		final TLCState teNextState = teStates.get(next);
		assertFalse(teNextState.isInitialState());
		assertEquals(mcNextState.getLabel(), teNextState.getLabel());
		assertEquals(mcNextState.getStateNumber(), teNextState.getStateNumber());
		assertEquals(mcNextState.getVariableCount(1) + 2, teNextState.getVariableCount(1));
		final Map<String, TLCVariable> teNextDiff = teNextState.getDiff(mcNextState);
		assertEquals(2, teNextDiff.size());
		assertEquals(teNextDiff.get(TLAConstants.TraceExplore.POSITION).toString(), "2");
		assertEquals(teNextDiff.get("store = <<>>").toString(), "FALSE");
	}

	private static final Hashtable<String, TraceExpressionInformationHolder> getTraceExpressionDataTable() {
		final Hashtable<String, TraceExpressionInformationHolder> hashtable = new Hashtable<String, TraceExpressionInformationHolder>();
		hashtable.put("__trace_var_155717784845014000", new TraceExpressionInformationHolder(TLAConstants.TraceExplore.POSITION, null, "__trace_var_155717784845014000"));

		final TraceExpressionInformationHolder value = new TraceExpressionInformationHolder("store = <<>>", null, "__trace_var_155717784845012000");
		value.setLevel(1);
		hashtable.put(value.getVariableName(), value);
		
		return hashtable;
	}
	
	//*********************************************//
	
	@Test
	public void testXA() {
		testX(Order.OneToN, Order.NToOne, 0, 1);
	}
	@Test
	public void testXB() {
		testX(Order.NToOne, Order.OneToN, 2, 1);
	}
	@Test
	public void testXC() {
		testX(Order.OneToN, Order.OneToN, 0, 1);
	}
	@Test
	public void testXD() {
		testX(Order.NToOne, Order.NToOne, 2, 1);
	}
	
	private static void testX(final Order sortMC, final Order sortTE, final int init, final int next) {
		final String modelName = "Model_1";
		final Map<String, Formula> traceExplorerExpressions = new HashMap<String, Formula>();
		final Hashtable<String, TraceExpressionInformationHolder> traceExpressionDataTable = getTraceExpressionDataTableX();
		
		// error origination for a "regular" TLC run.
		final TLCError mcError = new TLCError(sortMC);
		final TLCState mcInitState = TLCState.parseState("1: <Initial predicate>\n" + "x = 0", modelName);
		mcError.addState(mcInitState);
		final TLCState mcNextState = TLCState
				.parseState("2: <Next line 6, col 9 to line 6, col 40 of module Counter>\n" + "x = 1", modelName);
		mcError.addState(mcNextState);
		final TLCState mcLoopState = TLCState
				.parseState("1: Back to state: <Next line 6, col 9 to line 6, col 40 of module Counter>", modelName);
		mcError.addState(mcLoopState);
		
		// error originating from a trace expression evaluation.
		final TLCError teError = new TLCError(sortTE);
		teError.addState(TLCState.parseState(
				"1: <Initial predicate>\n/\\ __trace_var_15571917867925000 = \"--\"\n/\\ x = 0", modelName));
		teError.addState(
				TLCState.parseState("2: <next_15571917867927000 line 34, col 2 to line 42, col 1 of module TE>\n"
						+ "/\\ __trace_var_15571917867925000 = TRUE\n/\\ x = 1", modelName));
		teError.addState(
				TLCState.parseState("3: <next_15571917867927000 line 44, col 2 to line 52, col 1 of module TE>\n"
						+ "/\\ __trace_var_15571917867925000 = FALSE\n" + "/\\ x = 0", modelName));
		teError.addState(TLCState.parseState(
				"2: Back to state: <next_15571917867927000 line 34, col 2 to line 42, col 1 of module TE>", modelName));
		
		// Merge teError with mcError
		teError.applyFrom(mcError, traceExplorerExpressions, traceExpressionDataTable, modelName);
		
		final List<TLCState> teStates = teError.getStates();
		assertEquals(3, teStates.size());
		
		final TLCState teInitState = teStates.get(init);
		assertTrue(teInitState.isInitialState());
		assertEquals(mcInitState.getLabel(), teInitState.getLabel());
		assertEquals(mcInitState.getStateNumber(), teInitState.getStateNumber());
		final Map<String, TLCVariable> teInitDiff = teInitState.getDiff(mcInitState);
		assertEquals(2, teInitDiff.size());
		assertEquals(teInitDiff.get("x' > x").toString(), "\"--\"");

		final TLCState teNextState = teStates.get(next);
		assertFalse(teNextState.isInitialState());
		assertEquals(mcNextState.getLabel(), teNextState.getLabel());
		assertEquals(mcNextState.getStateNumber(), teNextState.getStateNumber());
		final Map<String, TLCVariable> teNextDiff = teNextState.getDiff(mcNextState);
		assertEquals(2, teNextDiff.size());
		assertEquals(teNextDiff.get("x' > x").toString(), "TRUE");
	}

	private static final Hashtable<String, TraceExpressionInformationHolder> getTraceExpressionDataTableX() {
		final Hashtable<String, TraceExpressionInformationHolder> hashtable = new Hashtable<String, TraceExpressionInformationHolder>();

		final TraceExpressionInformationHolder value = new TraceExpressionInformationHolder("x' > x", null, "__trace_var_15571917867925000");
		value.setLevel(1);
		hashtable.put(value.getVariableName(), value);
		
		return hashtable;
	}
}
