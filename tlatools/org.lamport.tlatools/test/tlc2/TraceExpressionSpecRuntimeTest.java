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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Map;

import tlc2.output.EC;
import tlc2.tool.Action;
import tlc2.tool.StateVec;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.Tool;
import tlc2.util.Vect;
import tlc2.value.IValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;

public class TraceExpressionSpecRuntimeTest extends TraceExpressionSpecTest {

	private static final String TE_SPEC_TEST = "TESpecRuntimeErrorTest";

	public TraceExpressionSpecRuntimeTest() {
		super(TE_SPEC_TEST, "TESpecRuntimeErrorTest.cfg", "-modelcheck", EC.ExitStatus.FAILURE_SPEC_EVAL);
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
		assertEquals(new RecordValue("val", IntValue.gen(0)), vals.get("x"));

		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		assertTrue(tool.isValid(invariants[0], sv.first()));
		vals = sv.first().getVals();
		assertEquals(new RecordValue("val", IntValue.gen(1)), vals.get("x"));

		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		assertTrue(tool.isValid(invariants[0], sv.first()));
		vals = sv.first().getVals();
		assertEquals(new RecordValue("val", IntValue.gen(2)), vals.get("x"));

		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		assertTrue(tool.isValid(invariants[0], sv.first()));
		vals = sv.first().getVals();
		assertEquals(new RecordValue("val", IntValue.gen(3)), vals.get("x"));

		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		assertFalse(tool.isValid(invariants[0], sv.first()));
		vals = sv.first().getVals();
		assertEquals(new RecordValue("val2", IntValue.gen(4)), vals.get("x"));

		assertNotNull(tool.getModelConfig().getAlias());
		assertFalse(tool.getModelConfig().getCheckDeadlock());
	}
}
