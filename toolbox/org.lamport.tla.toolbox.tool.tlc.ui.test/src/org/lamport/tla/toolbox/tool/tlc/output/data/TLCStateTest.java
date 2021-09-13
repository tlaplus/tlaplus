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

		// Variables are returned in lexicographical ordering.
		final TLCVariable[] variables = state.getVariables();
		
		TLCVariable variable = variables[0];
		assertEquals("adding", variable.getName());
		TLCVariableValue expected = TLCVariableValue.parseValue("(e1 :> NotAnElement @@ e2 :> NotAnElement)");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[2];
		assertEquals("deq", variable.getName());
		expected = TLCVariableValue.parseValue("(d1 :> v1)");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[3];
		assertEquals("enq", variable.getName());
		expected = TLCVariableValue.parseValue("(e1 :> Done @@ e2 :> Done)");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[1];
		assertEquals("after", variable.getName());
		expected = TLCVariableValue.parseValue("<<>>");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());
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
		
		// Variables are returned in lexicographical ordering.
		final TLCVariable[] variables = state.getVariables();
		
		TLCVariable variable = variables[0];
		assertEquals("BackupLock", variable.getName());
		TLCVariableValue expected = TLCVariableValue.parseValue("None");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[2];
		assertEquals("IsNodeUp", variable.getName());
		expected = TLCVariableValue.parseValue("(n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[3];
		assertEquals("IsTakingBackup", variable.getName());
		expected = TLCVariableValue.parseValue("(n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[1];
		assertEquals("LockTimeout", variable.getName());
		expected = TLCVariableValue.parseValue("FALSE");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());
		
		variable = variables[4];
		assertEquals("NetworkPath", variable.getName());
		expected = TLCVariableValue.parseValue("( <<n1, n1>> :> TRUE @@\n"
				+ "  <<n1, n2>> :> TRUE @@\n" 
				+ "  <<n1, n3>> :> TRUE @@\n" 
				+ "  <<n2, n1>> :> TRUE @@\n" 
				+ "  <<n2, n2>> :> TRUE @@\n" 
				+ "  <<n2, n3>> :> TRUE @@\n" 
				+ "  <<n3, n1>> :> TRUE @@\n" 
				+ "  <<n3, n2>> :> TRUE @@\n" 
				+ "  <<n3, n3>> :> TRUE )");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());
	}

	@Test
	public void testStuttering() {
		final TLCState state = TLCState.parseState("2: Stuttering", "Model_1");
		assertFalse(state.isBackToState());
		assertTrue(state.isStuttering());

		assertEquals(2, state.getStateNumber());
		
		assertEquals(0, state.getVariablesAsList().size());
	}

	@Test
	public void testBackToState() {
		final TLCState state = TLCState.parseState(
				"3: Back to state: <Action line 102, col 16 to line 104, col 50 of module NQSpec>", "Model_1");
		assertTrue(state.isBackToState());
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
		assertFalse(state.isBackToState());
		assertFalse(state.isStuttering());
		
		assertEquals(2, state.getStateNumber());
		
		// Variables are returned in lexicographical ordering.
		final TLCVariable[] variables = state.getVariables();
		
		TLCVariable variable = variables[0];
		assertEquals("adding", variable.getName());
		TLCVariableValue expected = TLCVariableValue.parseValue("(e1 :> [data |-> v2, id |-> i2] @@ e2 :> NotAnElement)");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[2];
		assertEquals("deq", variable.getName());
		expected = TLCVariableValue.parseValue("(d1 :> v1)");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[3];
		assertEquals("enq", variable.getName());
		expected = TLCVariableValue.parseValue("(e1 :> v2 @@ e2 :> Done)");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[1];
		assertEquals("after", variable.getName());
		expected = TLCVariableValue.parseValue("([data |-> v2, id |-> i2] :> {})");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

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
			assertFalse(state.isBackToState());
			assertFalse(state.isStuttering());
			
			assertEquals(2, state.getStateNumber());
			
			// Variables are returned in lexicographical ordering.
			final TLCVariable[] variables = state.getVariables();
			
			TLCVariable variable = variables[0];
			assertEquals("BackupLock", variable.getName());
			TLCVariableValue expected = TLCVariableValue.parseValue("None");
			variable.getValue().diff(expected);
			assertFalse(expected.isChanged());

			variable = variables[1];
			assertEquals("IsNodeUp", variable.getName());
			expected = TLCVariableValue.parseValue("(n1 :> TRUE @@ n2 :> TRUE @@ n3 :> TRUE)");
			variable.getValue().diff(expected);
			assertFalse(expected.isChanged());

			variable = variables[2];
			assertEquals("IsTakingBackup", variable.getName());
			expected = TLCVariableValue.parseValue("(n1 :> FALSE @@ n2 :> FALSE @@ n3 :> FALSE)");
			variable.getValue().diff(expected);
			assertFalse(expected.isChanged());

			variable = variables[3];
			assertEquals("Leader", variable.getName());
			expected = TLCVariableValue.parseValue("n1");
			variable.getValue().diff(expected);
			assertFalse(expected.isChanged());

			variable = variables[4];
			assertEquals("LockTimeout", variable.getName());
			expected = TLCVariableValue.parseValue("FALSE");
			variable.getValue().diff(expected);
			assertFalse(expected.isChanged());

			variable = variables[5];
			assertEquals("NetworkPath", variable.getName());
			expected = TLCVariableValue.parseValue("( <<n1, n1>> :> TRUE @@\n"
					+ "  <<n1, n2>> :> TRUE @@\n" 
					+ "  <<n1, n3>> :> TRUE @@\n" 
					+ "  <<n2, n1>> :> TRUE @@\n" 
					+ "  <<n2, n2>> :> TRUE @@\n" 
					+ "  <<n2, n3>> :> TRUE @@\n" 
					+ "  <<n3, n1>> :> TRUE @@\n" 
					+ "  <<n3, n2>> :> TRUE @@\n" 
					+ "  <<n3, n3>> :> TRUE )");
			variable.getValue().diff(expected);
			assertFalse(expected.isChanged());
			
			assertEquals(state.getModuleLocation(), new Location(UniqueString.uniqueStringOf("NodeBackup"), 138, 24, 138, 37));
	}

	@Test
	public void testStateEqualsInStrings() {
		final String input = "2: <Next line 6, col 9 to line 6, col 24 of module Github670>\n"
				+ "v = \"foo = bar\"\n";

		final TLCState state = TLCState.parseState(input, "Model_1");
		assertFalse(state.isBackToState());
		assertFalse(state.isStuttering());
		
		assertEquals(2, state.getStateNumber());
		
		// Variables are returned in lexicographical ordering.
		final TLCVariable[] variables = state.getVariables();
		TLCVariable variable = variables[0];
		assertEquals("v", variable.getName());
		TLCVariableValue expected = TLCVariableValue.parseValue("\"foo = bar\"");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		
		assertEquals(state.getModuleLocation(), new Location(UniqueString.uniqueStringOf("Github670"), 6, 9, 6, 24));
	}

	@Test
	public void testStateEqualsInStringsMultiline() {
		final String input = "2: <Next line 6, col 9 to line 6, col 24 of module Github670>\n" +
				"/\\ NetworkPath = ( <<n1, n1>> :> TRUE @@\n" +
				"  <<n1, n2>> :> TRUE @@\n" +
				"  <<n1, n3>> :> TRUE @@\n" +
				"  <<n2, n1>> :> TRUE @@\n" +
				"  <<n2, n2>> :> TRUE @@\n" +
				"  <<n2, n3>> :> TRUE @@\n" +
				"  <<n3, n1>> :> TRUE @@\n" +
				"  <<n3, n2>> :> TRUE @@\n" +
				"  <<n3, n3>> :> TRUE )\n" 
				+ "/\\ VPol = [col_submissions_submission_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_submissions_paper_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_submissions_conference_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_submissions_submission_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_submissions_status |-> [policy |-> {<<x, <<[t_expire |-> {}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>, <<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {x}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_paper_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_title |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_abstract |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_text |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_authors |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_logs_event_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_logs_err_info |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_conference_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_name |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_start_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_end_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_description |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_paper_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_title |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_start_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_end_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_description |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_allocations_allocation_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_allocations_paper_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_allocations_section_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_allocations_allocation_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0]]\n"
				+ "/\\ XLocks = jorge\n"
				+ "/\\ Trace = <<<<allen, \"p_change_status_load\", \"change_status_load\", [from |-> <<<<\"c11\">>, <<\"c12\">>>>, to |-> <<[policy |-> {<<allen, <<[t_expire |-> {NONE}], [reviewer |-> {allen}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 0, loc |-> \"mem\"], [policy |-> {<<allen, <<[t_expire |-> {NONE}], [reviewer |-> {allen}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 1, loc |-> \"mem\"]>>]>>, <<allen, \"p_change_status4\", \"update SUBMISSIONS set STATUS = stat where SUBMISSION_ID = s_id\", [from |-> <<<<[policy |-> {<<allen, <<[t_expire |-> {NONE}], [reviewer |-> {allen}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 1, loc |-> \"mem\"], [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, loc |-> \"persistence\"], [policy |-> {<<allen, <<[t_expire |-> {NONE}], [reviewer |-> {allen}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 0, loc |-> \"mem\"]>>>>, to |-> <<[policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, loc |-> \"persistence\"]>>]>>, <<allen, \"p_change_status_exit\", \"change_status_exit\", [from |-> <<>>, to |-> <<>>]>>, <<jorge, \"p_allocate_load\", \"allocate_load\">>, <<jorge, \"f_is_accepted_call\", \"is_accepted_call\">>, <<jorge, \"f_is_accepted5\", \"SELECT STATUS into v_status, FROM SUBMISSIONS WHERE SUBMISSION_ID = s_id\", [from |-> <<<<[policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, loc |-> \"persistence\"], [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, loc |-> \"persistence\"], [policy |-> {<<jorge, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 0, loc |-> \"mem\"]>>>>, to |-> <<[policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 1, loc |-> \"mem\"]>>]>>, <<jorge, \"f_is_accepted8\", \"if v_status = 1\", [from |-> <<<<[policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 1, loc |-> \"mem\"], \"c14\">>>>, to |-> <<<<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>>>]>>>>\n"
				+ "/\\ Ignore = 0\n"
				+ "/\\ StateE = [reviewer |-> {}, organizer |-> {}, manager |-> {}, guest |-> {}, t_expire |-> {}]\n"
				+ "/\\ SLocks = (allen :> [reviewer |-> {}, organizer |-> {}, manager |-> {}, guest |-> {}, t_expire |-> {}] @@ jorge :> [reviewer |-> {}, organizer |-> {}, manager |-> {}, guest |-> {}, t_expire |-> {}] @@ bob :> [reviewer |-> {}, organizer |-> {}, manager |-> {}, guest |-> {}, t_expire |-> {}])\n"
				+ "/\\ New2Old = <<<<{}>>, <<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>>>\n"
				+ "/\\ Sessions = (allen :> [SessionM |-> <<>>, PCLabel |-> <<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>, Ret |-> Undef, StateRegs |-> <<>>] @@ jorge :> [SessionM |-> <<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>, <<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {x}, guest |-> {NONE}]>>>>}, {<<jorge, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {jorge}, guest |-> {NONE}]>>>>}>>, PCLabel |-> <<{<<x, <<[t_expire |-> {}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>, <<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {x}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>, Ret |-> Undef, StateRegs |-> <<[pc |-> <<\"f_is_accepted\", \"lbl_9_10\">>, fp |-> 8], [pc |-> <<\"p_allocate\", \"lbl_7r\">>, fp |-> 1]>>] @@ bob :> [SessionM |-> <<>>, PCLabel |-> <<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>, Ret |-> Undef, StateRegs |-> <<[pc |-> <<\"f_get_section_program\", \"lbl_5\">>, fp |-> 1]>>])";

		final TLCState state = TLCState.parseState(input, "Model_1");
		assertFalse(state.isBackToState());
		assertFalse(state.isStuttering());
		
		assertEquals(2, state.getStateNumber());
		
		// Variables are returned in lexicographical ordering.
		final TLCVariable[] variables = state.getVariables();
		
		int i = 0;
		
		TLCVariable variable = variables[i++];
		assertEquals("Ignore", variable.getName());
		TLCVariableValue expected = TLCVariableValue.parseValue("0");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[i++];
		assertEquals("NetworkPath", variable.getName());
		expected = TLCVariableValue.parseValue("( <<n1, n1>> :> TRUE @@\n"
				+ "  <<n1, n2>> :> TRUE @@\n" 
				+ "  <<n1, n3>> :> TRUE @@\n" 
				+ "  <<n2, n1>> :> TRUE @@\n" 
				+ "  <<n2, n2>> :> TRUE @@\n" 
				+ "  <<n2, n3>> :> TRUE @@\n" 
				+ "  <<n3, n1>> :> TRUE @@\n" 
				+ "  <<n3, n2>> :> TRUE @@\n" 
				+ "  <<n3, n3>> :> TRUE )");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[i++];
		assertEquals("New2Old", variable.getName());
		expected = TLCVariableValue.parseValue(
				"<<<<{}>>, <<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>>>");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());
		
		variable = variables[i++];
		assertEquals("SLocks", variable.getName());
		expected = TLCVariableValue.parseValue(
				"(allen :> [reviewer |-> {}, organizer |-> {}, manager |-> {}, guest |-> {}, t_expire |-> {}] @@ jorge :> [reviewer |-> {}, organizer |-> {}, manager |-> {}, guest |-> {}, t_expire |-> {}] @@ bob :> [reviewer |-> {}, organizer |-> {}, manager |-> {}, guest |-> {}, t_expire |-> {}])");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[i++];
		assertEquals("Sessions", variable.getName());
		expected = TLCVariableValue.parseValue(
				"(allen :> [SessionM |-> <<>>, PCLabel |-> <<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>, Ret |-> Undef, StateRegs |-> <<>>] @@ jorge :> [SessionM |-> <<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>, <<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {x}, guest |-> {NONE}]>>>>}, {<<jorge, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {jorge}, guest |-> {NONE}]>>>>}>>, PCLabel |-> <<{<<x, <<[t_expire |-> {}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>, <<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {x}, guest |-> {NONE}]>>>>}, {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>, Ret |-> Undef, StateRegs |-> <<[pc |-> <<\"f_is_accepted\", \"lbl_9_10\">>, fp |-> 8], [pc |-> <<\"p_allocate\", \"lbl_7r\">>, fp |-> 1]>>] @@ bob :> [SessionM |-> <<>>, PCLabel |-> <<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>, Ret |-> Undef, StateRegs |-> <<[pc |-> <<\"f_get_section_program\", \"lbl_5\">>, fp |-> 1]>>])");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[i++];
		assertEquals("StateE", variable.getName());
		expected = TLCVariableValue
				.parseValue("[reviewer |-> {}, organizer |-> {}, manager |-> {}, guest |-> {}, t_expire |-> {}]");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[i++];
		assertEquals("Trace", variable.getName());
		expected = TLCVariableValue.parseValue(
				"<<<<allen, \"p_change_status_load\", \"change_status_load\", [from |-> <<<<\"c11\">>, <<\"c12\">>>>, to |-> <<[policy |-> {<<allen, <<[t_expire |-> {NONE}], [reviewer |-> {allen}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 0, loc |-> \"mem\"], [policy |-> {<<allen, <<[t_expire |-> {NONE}], [reviewer |-> {allen}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 1, loc |-> \"mem\"]>>]>>, <<allen, \"p_change_status4\", \"update SUBMISSIONS set STATUS = stat where SUBMISSION_ID = s_id\", [from |-> <<<<[policy |-> {<<allen, <<[t_expire |-> {NONE}], [reviewer |-> {allen}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 1, loc |-> \"mem\"], [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, loc |-> \"persistence\"], [policy |-> {<<allen, <<[t_expire |-> {NONE}], [reviewer |-> {allen}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 0, loc |-> \"mem\"]>>>>, to |-> <<[policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, loc |-> \"persistence\"]>>]>>, <<allen, \"p_change_status_exit\", \"change_status_exit\", [from |-> <<>>, to |-> <<>>]>>, <<jorge, \"p_allocate_load\", \"allocate_load\">>, <<jorge, \"f_is_accepted_call\", \"is_accepted_call\">>, <<jorge, \"f_is_accepted5\", \"SELECT STATUS into v_status, FROM SUBMISSIONS WHERE SUBMISSION_ID = s_id\", [from |-> <<<<[policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, loc |-> \"persistence\"], [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, loc |-> \"persistence\"], [policy |-> {<<jorge, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 0, loc |-> \"mem\"]>>>>, to |-> <<[policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 1, loc |-> \"mem\"]>>]>>, <<jorge, \"f_is_accepted8\", \"if v_status = 1\", [from |-> <<<<[policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, offs |-> 1, loc |-> \"mem\"], \"c14\">>>>, to |-> <<<<{<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}>>>>]>>>>");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[i++];
		assertEquals("VPol", variable.getName());
		expected = TLCVariableValue.parseValue(
				"[col_submissions_submission_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_submissions_paper_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_submissions_conference_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_submissions_submission_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_submissions_status |-> [policy |-> {<<x, <<[t_expire |-> {}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>, <<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {x}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_paper_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_title |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_abstract |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_text |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_papers_authors |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_logs_event_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_logs_err_info |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_conference_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_name |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_start_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_end_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_conferences_description |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_paper_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_title |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_start_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_end_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_sections_description |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_allocations_allocation_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_allocations_paper_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_allocations_section_id |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0], col_allocations_allocation_date |-> [policy |-> {<<x, <<[t_expire |-> {NONE}], [reviewer |-> {NONE}, organizer |-> {NONE}, manager |-> {NONE}, guest |-> {NONE}]>>>>}, ext |-> 0]]");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());

		variable = variables[i++];
		assertEquals("XLocks", variable.getName());
		expected = TLCVariableValue.parseValue("jorge");
		variable.getValue().diff(expected);
		assertFalse(expected.isChanged());
		
		assertEquals(state.getModuleLocation(), new Location(UniqueString.uniqueStringOf("Github670"), 6, 9, 6, 24));
	}
}
