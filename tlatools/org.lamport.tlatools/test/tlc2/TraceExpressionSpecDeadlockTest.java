/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Map;

import tla2sany.semantic.ExternalModuleTable;
import tlc2.output.EC;
import tlc2.tool.Action;
import tlc2.tool.StateVec;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.Tool;
import tlc2.util.Vect;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import util.TLAConstants;

public class TraceExpressionSpecDeadlockTest extends TraceExpressionSpecTest {

	private static final String TE_SPEC_TEST = "TESpecDeadlockTest";

	public TraceExpressionSpecDeadlockTest() {
		super(TE_SPEC_TEST, "TESpecDeadlockTest", "-modelcheck", EC.ExitStatus.VIOLATION_DEADLOCK);
	}

	@Override
	protected boolean checkDeadLock() {
		return true;
	}

	@Override
	protected void doTest(final Tool tool, final String id) {
		final SpecProcessor specProcessor = tool.getSpecProcessor();

		Action[] actions = tool.getActions();
		assertEquals(1, actions.length);

		// Assert that one invariant exists.
		final Action[] invariants = specProcessor.getInvariants();
		assertEquals(1, invariants.length);

		// Assert there exists one init-predicate
		Vect<Action> initPred = specProcessor.getInitPred();
		assertEquals(1, initPred.size());

		// Assert there exists a next-state relation
		assertNotNull(specProcessor.getNextPred());

		// Assert the trace
		StateVec sv = tool.getInitStates();
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		assertTrue(tool.isValid(invariants[0], sv.first()));
		Map<String, IValue> vals = sv.first().getVals();
		assertEquals(IntValue.gen(0), vals.get("x"));
		assertEquals(BoolValue.ValFalse, vals.get("y"));

		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		assertTrue(tool.isValid(invariants[0], sv.first()));
		vals = sv.first().getVals();
		assertEquals(IntValue.gen(1), vals.get("x"));
		assertEquals(BoolValue.ValTrue, vals.get("y"));

		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		assertTrue(tool.isValid(invariants[0], sv.first()));
		vals = sv.first().getVals();
		assertEquals(IntValue.gen(2), vals.get("x"));
		assertEquals(BoolValue.ValFalse, vals.get("y"));

		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		assertTrue(tool.isValid(invariants[0], sv.first()));
		vals = sv.first().getVals();
		assertEquals(IntValue.gen(3), vals.get("x"));
		assertEquals(BoolValue.ValTrue, vals.get("y"));

		assertNotNull(tool.getModelConfig().getAlias());

		//TODO: We want the spec to deadlock and not violate an artificial invariant.
//		assertTrue(tool.getModelConfig().getCheckDeadlock());
		
		// Assert that all three sub-modules exist
		final ExternalModuleTable moduleTbl = specProcessor.getModuleTbl();
		assertNotNull(moduleTbl.getModuleNode(TE_SPEC_TEST));
		assertNotNull(moduleTbl.getModuleNode(TE_SPEC_TEST + "_" + TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME));
		assertNotNull(moduleTbl.getModuleNode(TE_SPEC_TEST + "_" + TLAConstants.TraceExplore.SPEC_TETRACE_NAME));
	}
}
