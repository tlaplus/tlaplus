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
import static org.junit.Assert.fail;

import java.util.Map;

import tla2sany.semantic.ExternalModuleTable;
import tlc2.output.EC;
import tlc2.tool.Action;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.Tool;
import tlc2.tool.liveness.LiveCheck1;
import tlc2.tool.liveness.LiveException;
import tlc2.util.SetOfStates;
import tlc2.util.Vect;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import util.TLAConstants;
import util.UniqueString;

public class TraceExpressionSpecLassoTest extends TraceExpressionSpecTest {

	private static final String TE_SPEC_TEST = "TESpecTest";

	public TraceExpressionSpecLassoTest() {
		super(TE_SPEC_TEST, "TESpecLassoTest.cfg", "-modelcheck", EC.ExitStatus.VIOLATION_LIVENESS);
	}

	protected double getLivenessThreshold() {
		return TLCGlobals.livenessThreshold; // don't change the default
	}

	@Override
	protected void doTest(final Tool tool, final String id) throws Exception {
		final SpecProcessor specProcessor = tool.getSpecProcessor();

		Action[] actions = tool.getActions();
		assertEquals(1, actions.length);

		assertEquals(0, specProcessor.getInvariants().length);
		
		// Assert that one property exists.
		final Action[] property = specProcessor.getImpliedTemporals();
		assertEquals(1, property.length);

		// Assert there exists one init-predicate
		Vect<Action> initPred = specProcessor.getInitPred();
		assertEquals(1, initPred.size());

		// Assert there exists a next-state relation
		assertNotNull(specProcessor.getNextPred());
		
		assertNotNull(tool.getModelConfig().getAlias());
		assertFalse(tool.getModelConfig().getCheckDeadlock());
		
		// Assert that all three sub-modules exist
		final ExternalModuleTable moduleTbl = specProcessor.getModuleTbl();
		assertNotNull(moduleTbl.getModuleNode(UniqueString.of(TE_SPEC_TEST)));
		assertNotNull(moduleTbl.getModuleNode(
				UniqueString.of(TE_SPEC_TEST + "_" + TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME)));
		assertNotNull(moduleTbl.getModuleNode(UniqueString.of(TE_SPEC_TEST + "_" + TLAConstants.TraceExplore.SPEC_TETRACE_NAME)));

		final LiveCheck1 lc = new LiveCheck1(tool);
		lc.init(tool, tool.getActions(), "states");
		
		// Assert the trace
		StateVec sv = tool.getInitStates();
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		Map<UniqueString, IValue> vals = sv.first().getVals();
		assertEquals(IntValue.gen(0), vals.get(UniqueString.of("x")));
		assertEquals(BoolValue.ValFalse, vals.get(UniqueString.of("y")));
		lc.addInitState(tool, sv.first(), sv.first().fingerPrint());
		TLCState cur = sv.first();

		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		vals = sv.first().getVals();
		assertEquals(IntValue.gen(1), vals.get(UniqueString.of("x")));
		assertEquals(BoolValue.ValTrue, vals.get(UniqueString.of("y")));

		SetOfStates nextStates = new SetOfStates(1);
		nextStates.put(sv.first());
		lc.addNextState(tool, cur, cur.fingerPrint(), nextStates);
		cur = sv.first();
		
		sv = tool.getNextStates(actions[0], sv.first());
		assertEquals(1, sv.size());
		assertTrue(tool.isGoodState(sv.first()));
		assertTrue(tool.isInModel(sv.first()));
		vals = sv.first().getVals();
		assertEquals(IntValue.gen(0), vals.get(UniqueString.of("x")));
		assertEquals(BoolValue.ValFalse, vals.get(UniqueString.of("y")));

		nextStates = new SetOfStates(1);
		nextStates.put(sv.first());
		lc.addNextState(tool, cur, cur.fingerPrint(), nextStates);
		
		try {
			lc.finalCheck(tool);
		} catch (LiveException e) {
			return;
		}
		fail();
	}
}
