/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
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
package tlc2.debug;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.lsp4j.debug.StackFrame;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.util.Context;
import tlc2.value.impl.IntValue;

public class EWD840SteppingDebuggerSimTest extends TLCDebuggerTestCase {

	// MC02 is the spec that extends EWD840 and assigns values to constants for TLC.
	private static final String RM = "EWD840";
	private static final String MDL = "MC03Sim";

	public EWD840SteppingDebuggerSimTest() {
		super(MDL, RM, new String[] { "-config", "MC03Sim.cfg", "-simulate", "num=1", "-depth", "25", "-seed", "111123", "-fp", "1" },
				EC.ExitStatus.VIOLATION_DEADLOCK);
	}

	@Override
	protected boolean checkDeadLock() {
		return true;
	}

	@Test
	public void testSpec() throws Exception {
		// A "Next" breakpoint, i.e. a breakpoint that fires when a state has been
		// generated.
		debugger.replaceAllBreakpointsWith(RM, 68);

		StackFrame[] stackFrames = debugger.continue_();
		TLCActionStackFrame f = assertTLCActionFrame(stackFrames[0], 48, 6, 48, 31, RM,
				Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne));
		assertTrue(f.getT().allAssigned());
		assertEquals(2, f.getT().getLevel());

		// Stepping out of the first action lands us at another action with level 1 -> 2.
		stackFrames = debugger.stepOut();
		f = assertTLCActionFrame(stackFrames[0], 31, 6, 31, 25, RM, Context.Empty);
		assertTrue(f.getT().allAssigned());
		assertEquals(2, f.getT().getLevel());
		TLCState state = f.getT();

		stackFrames = debugger.stepIn();
		f = (TLCActionStackFrame) stackFrames[0];
		assertEquals(state, f.getS());
		assertTrue(f.getT().allAssigned());
		assertEquals(3, f.getT().getLevel());
		state = f.getT();

		stackFrames = debugger.stepIn();
		f = (TLCActionStackFrame) stackFrames[0];
		assertEquals(state, f.getS());
		assertTrue(f.getT().allAssigned());
		assertEquals(4, f.getT().getLevel());
		state = f.getT();

		stackFrames = debugger.next();
		f = (TLCActionStackFrame) stackFrames[0];
		assertNotSame(state, f.getS()); // Skipped state with next.
		assertTrue(f.getT().allAssigned());
		assertEquals(4, f.getT().getLevel());
		state = f.getT();
		
		// 888888888888888888888888888888888888888888

		// Step into TLCSuccessorStackFrame. Doesn't work yet to reverse from this kind
		// of breakpoint.
//		debugger.unsetBreakpoints();
//		debugger.setBreakpoints(createBreakpointArgument(RM, 33, 4, 1));
//		stackFrames = debugger.continue_();
//		TLCSuccessorsStackFrame g = (TLCSuccessorsStackFrame) stackFrames[stackFrames.length - 1];		
//		assertEquals(g.getS(), g.getT());
//		assertTrue(g.getS().allAssigned());
//		assertEquals(5, g.getT().getLevel());
//		assertEquals(1, g.getSuccessors().size());

		// Reverse out of an ordinary breakpoint.
		debugger.replaceAllBreakpointsWith(RM, 40);
		stackFrames = debugger.continue_();
		f = (TLCActionStackFrame) stackFrames[0];
		assertEquals(5, f.getS().getLevel());
		assertEquals(6, f.getT().getLevel());

		stackFrames = debugger.reverseContinue();
		TLCSuccessorsStackFrame g = (TLCSuccessorsStackFrame) stackFrames[0];		
		assertEquals(g.getS(), g.getT());
		assertTrue(g.getS().allAssigned());
		assertEquals(5, g.getT().getLevel());
		assertEquals(0, g.getSuccessors().size());
		
		// 888888888888888888888888888888888888888888
		
		// Back to the start
		debugger.replaceAllBreakpointsWith(RM, 68);
		stackFrames = debugger.continue_();
		stackFrames = debugger.continue_();
		
		stackFrames = debugger.stepOut(5);
		f = (TLCActionStackFrame) stackFrames[0];
		assertTrue(f.getT().allAssigned());
		assertEquals(2, f.getT().getLevel());
		state = f.getT();
				
		// 888888888888888888888888888888888888888888

		// Let's deadlock state-space exploration by skipping over all successors.
		final Set<TLCState> skipped = new HashSet<TLCState>();
		skipped.add(state);
		final TLCState init = f.getS();
		
		for (int i = 0; i < 10; i++) {
			stackFrames = debugger.next();
			f = (TLCActionStackFrame) stackFrames[0];
			assertEquals(init, f.getS());
			assertNotSame(state, f.getS()); // Skipped state with next.
			assertTrue(f.getT().allAssigned());
			assertEquals(2, f.getT().getLevel());
			assertTrue(skipped.add(f.getT()));
		}
		stackFrames = debugger.next();

		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_PROGRESS_SIMU, "1030", "1", "0", "0", "0"));
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(7);
		expectedTrace.add(
				"/\\ tpos = 0\n"
				+ "/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE @@ 4 :> TRUE)\n"
				+ "/\\ tcolor = \"black\"\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"black\" @@ 4 :> \"black\")");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
	}
}
