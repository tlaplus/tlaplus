/*******************************************************************************
 * Copyright (c) 2024 Microsoft Corp. All rights reserved. 
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

package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;

import org.junit.Test;

import tla2sany.semantic.SemanticNode;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.util.DotStateWriter;
import tlc2.util.IStateWriter;
import util.FileUtil;

public class DotConstrainedTest extends ModelCheckerTestCase {

	public DotConstrainedTest() {
		super("Github602",
				new String[] { "-config", "DotConstrained.cfg", "-dump", "dot,constrained",
						"${metadir}" + FileUtil.separator + DotConstrainedTest.class.getCanonicalName() + ".dot" },
				ExitStatus.VIOLATION_SAFETY);
	}

	@Override
	protected boolean doDump() {
		// Explicitly passed -dump command in constructor.
		return false;
	}

	private final AtomicBoolean constrained = new AtomicBoolean(false);
	
	@Override
	protected IStateWriter getStateWriter(final IStateWriter sw) {
		try {
			return new DotStateWriter(sw.getDumpFileName(), "strict ", false, false, false, true, false, false) {
				@Override
				public void writeState(final TLCState state, final TLCState successor, final short stateFlags,
						Action action, SemanticNode pred) {
					super.writeState(state, successor, stateFlags, action, pred);
					if (isSet(stateFlags, IStateWriter.IsNotInModel)) {
						constrained.set(true);
					}
				}
			};
		} catch (IOException e) {
			fail(e.getMessage());
			return null;
		}
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "4", "2", "0"));

		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));

		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(3);
		expectedTrace.add("x = 0");
		expectedTrace.add("x = 1");
		expectedTrace.add("x = -1");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
		
		assertTrue(constrained.get());
		
		assertZeroUncovered();
	}
}
