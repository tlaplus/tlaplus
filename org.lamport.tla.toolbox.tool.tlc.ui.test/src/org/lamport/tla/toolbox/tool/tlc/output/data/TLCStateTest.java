/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Test;

import tla2sany.st.Location;
import util.UniqueString;

public class TLCStateTest {

	@Test
	public void testInitNQSpec() {
		final String input = "1: <Initial predicate>\n" +
						"/\\ adding = (e1 :> NotAnElement @@ e2 :> NotAnElement)\n" +
						"/\\ deq = (d1 :> v1)\n" +
						"/\\ enq = (e1 :> Done @@ e2 :> Done)\n" +
						"/\\ after = <<>>";

		final TLCState state = TLCState.parseState(input, "Model_1");
		assertTrue(state.isInitialState());
		assertFalse(state.isBackToState());
		assertFalse(state.isStuttering());
		
		assertEquals(1, state.getStateNumber());
		
		final List<TLCVariable> variables = state.getVariablesAsList();
		variables.contains(
				new TLCVariable("adding", TLCVariableValue.parseValue("(e1 :> NotAnElement @@ e2 :> NotAnElement)")));
		variables.contains(
				new TLCVariable("deq", TLCVariableValue.parseValue("(d1 :> v1)")));
		variables.contains(
				new TLCVariable("enq", TLCVariableValue.parseValue("(e1 :> Done @@ e2 :> Done)")));
		variables.contains(
				new TLCVariable("after", TLCVariableValue.parseValue("<<>>")));
	}
	
	public void testInitNodeBackup() {
		final String input = "1: <Initial predicate>\n" +
			"/\\ IsNodeUp = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)\n" +
			"/\\ NetworkPath = ( <<n1, n1>> :> TRUE @@\n" +
			 "  <<n1, n2>> :> TRUE @@\n" +
			 "  <<n1, n3>> :> TRUE @@\n" +
			 "  <<n2, n1>> :> TRUE @@\n" +
			 "  <<n2, n2>> :> TRUE @@\n" +
			 "  <<n2, n3>> :> TRUE @@\n" +
			 "  <<n3, n1>> :> TRUE @@\n" +
			 "  <<n3, n2>> :> TRUE @@\n" +
			 "  <<n3, n3>> :> TRUE )\n" +
			"/\\ LockTimeout = FALSE\n" +
			"/\\ BackupLock = None\n" +
			"/\\ IsTakingBackup = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)\n" +
			"/\\ Leader = None";

		final TLCState state = TLCState.parseState(input, "Model_1");
		assertTrue(state.isInitialState());
		assertFalse(state.isBackToState());
		assertFalse(state.isStuttering());
		
		assertEquals(1, state.getStateNumber());
		
		final List<TLCVariable> variables = state.getVariablesAsList();
		variables.contains(
				new TLCVariable("IsNodeUp", TLCVariableValue.parseValue("(n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)")));
		variables.contains(
				new TLCVariable("LockTimeout", TLCVariableValue.parseValue("FALSE")));
		variables.contains(
				new TLCVariable("BackupLock", TLCVariableValue.parseValue("None")));
		variables.contains(
				new TLCVariable("IsTakingBackup", TLCVariableValue.parseValue("(n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)")));
	}

	@Test
	public void testStuttering() {
		final TLCState state = TLCState.parseState("2: Stuttering", "Model_1");
		assertFalse(state.isBackToState());
		assertFalse(state.isInitialState());
		assertTrue(state.isStuttering());

		assertEquals(2, state.getStateNumber());
		
		assertEquals(0, state.getVariablesAsList().size());
	}

	@Test
	public void testBackToState() {
		final TLCState state = TLCState.parseState(
				"3: Back to state: <Action line 102, col 16 to line 104, col 50 of module NQSpec>", "Model_1");
		assertTrue(state.isBackToState());
		assertFalse(state.isInitialState());
		assertFalse(state.isStuttering());

		assertEquals(3, state.getStateNumber());
		
		assertEquals(0, state.getVariablesAsList().size());
		
		assertEquals(state.getModuleLocation(), new Location(UniqueString.uniqueStringOf("NQSpec"), 102, 16, 104, 50));
	}
	
	@Test
	public void testStateNQSpec() {
		final String input = "2: <Action line 88, col 16 to line 94, col 31 of module NQSpec>\n"+
			"/\\ adding = (e1 :> [data |-> v2, id |-> i2] @@ e2 :> NotAnElement)\n"+
			"/\\ deq = (d1 :> v1)\n"+
			"/\\ enq = (e1 :> v2 @@ e2 :> Done)\n"+
			"/\\ after = ([data |-> v2, id |-> i2] :> {})";

		final TLCState state = TLCState.parseState(input, "Model_1");
		assertFalse(state.isInitialState());
		assertFalse(state.isBackToState());
		assertFalse(state.isStuttering());
		
		assertEquals(2, state.getStateNumber());
		
		final List<TLCVariable> variables = state.getVariablesAsList();
		variables.contains(
				new TLCVariable("adding", TLCVariableValue.parseValue("(e1 :> [data |-> v2, id |-> i2] @@ e2 :> NotAnElement)")));
		variables.contains(
				new TLCVariable("deq", TLCVariableValue.parseValue("(d1 :> v1)")));
		variables.contains(
				new TLCVariable("enq", TLCVariableValue.parseValue("(e1 :> v2 @@ e2 :> Done)")));
		variables.contains(
				new TLCVariable("after", TLCVariableValue.parseValue("([data |-> v2, id |-> i2] :> {})")));
		
		assertEquals(state.getModuleLocation(), new Location(UniqueString.uniqueStringOf("NQSpec"), 88, 16, 94, 31));
	}
	
	@Test
	public void testStateNodeBackup() {
		final String input = "2: <Action line 138, col 24 to line 138, col 37 of module NodeBackup>\n" +
				"/\\ IsNodeUp = (n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)\n" +
				"/\\ NetworkPath = ( <<n1, n1>> :> TRUE @@\n" +
				"  <<n1, n2>> :> TRUE @@\n" +
				"  <<n1, n3>> :> TRUE @@\n" +
				"  <<n2, n1>> :> TRUE @@\n" +
				"  <<n2, n2>> :> TRUE @@\n" +
				"  <<n2, n3>> :> TRUE @@\n" +
				"  <<n3, n1>> :> TRUE @@\n" +
				"  <<n3, n2>> :> TRUE @@\n" +
				"  <<n3, n3>> :> TRUE )\n" +
				"/\\ LockTimeout = FALSE\n" +
				"/\\ BackupLock = None\n" +
				"/\\ IsTakingBackup = (n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)\n" +
				"/\\ Leader = n1";

			final TLCState state = TLCState.parseState(input, "Model_1");
			assertFalse(state.isInitialState());
			assertFalse(state.isBackToState());
			assertFalse(state.isStuttering());
			
			assertEquals(2, state.getStateNumber());
			
			final List<TLCVariable> variables = state.getVariablesAsList();
			variables.contains(
					new TLCVariable("IsNodeUp", TLCVariableValue.parseValue("(n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)")));
			variables.contains(
					new TLCVariable("LockTimeout", TLCVariableValue.parseValue("FALSE")));
			variables.contains(
					new TLCVariable("BackupLock", TLCVariableValue.parseValue("None")));
			variables.contains(
					new TLCVariable("IsTakingBackup", TLCVariableValue.parseValue("(n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)")));
			
			assertEquals(state.getModuleLocation(), new Location(UniqueString.uniqueStringOf("NodeBackup"), 138, 24, 138, 37));
	}
}
