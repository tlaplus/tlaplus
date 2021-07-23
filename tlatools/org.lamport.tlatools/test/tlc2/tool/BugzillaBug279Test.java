/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.value.Values;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SubsetValue;

/**
 * TLC bug caused by TLC's not preserving the semantics of CHOOSE
 * 
 *  Leslie Lamport 2012-03-08 00:26:08 UTC
 *  
 *  Running TLC on the spec written by Tom 
 *  Rodeheffer that I will attach finds a deadlock (as it should) and then 
 *  produces the following error when trying to generate the error trace:
 *  
 *      Failed to recover the initial state from its fingerprint.
 *      This is probably a TLC bug(2).
 *    
 *  The problem occurs because the value that TLC computes for a CHOOSE 
 *  depends on TLC's internal representation of its argument.  To compute 
 *  the 2nd state of the trace, TLC sets the variables 'set' and 'fun' to S1
 *  and  Ch(S1), respectively, where Ch(S1) equals CHOOSE of an expression 
 *  containing S1.   Fingerprinting that state causes TLC to canonicalize 
 *  the representation of the value of 'set', changing its representation of
 *  the value of S1.  When TLC constructs the error trace, it must 
 *  re-execute the spec to get the states in the trace.  When it tries to 
 *  compute the 2nd state of the trace, it uses the canonicalized 
 *  representation of S1, causing it to compute a different value of 
 *  variable 'set' than it did the first time, so it doesn't find a state 
 *  with the correct fingerprint as the next state of the trace.  (Note that
 *  the error message is misleading, since it's not the intiial state that 
 *  TLC fails to recover.)
 *  
 *  There seem to be two possible fixes.  The first is to canonicalize the 
 *  argument of CHOOSE whenever it is evaluated.  The second is to create a 
 *  separate deep copy of the state before fingerprinting it.  The first 
 *  seems like the best solution, since I can't think of any practical case 
 *  in which this would cause performance problems.  However, I will consult
 *  with Yuan Yu before doing anything about this.
 */
public class BugzillaBug279Test extends ModelCheckerTestCase {

	public BugzillaBug279Test() {
		super("InitStateBug", "Bug279", ExitStatus.VIOLATION_DEADLOCK);
	}
	
	@Override
	protected boolean checkDeadLock() {
		return true;
	}
	
	@Override
	protected boolean doDump() {
		// For this test, dumping means enumerating the SUBSETs which creates too much
		// overhead. The test is also about avoiding enumerating SUBSET. 
		return false;
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "3", "3", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_DEADLOCK_REACHED));
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(6);
		expectedTrace.add("/\\ set = {}\n/\\ pc = 0\n/\\ fun = {}");
		expectedTrace.add("/\\ set = SUBSET (1..20)\n/\\ pc = 1\n/\\ fun = {5}");
		expectedTrace.add(
				"/\\ set = " + Values.ppr(new SubsetValue(new IntervalValue(1, 8)).toSetEnum().normalize())
						+ "\n/\\ pc = 2\n/\\ fun = {5}");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
		
		assertZeroUncovered();
	}
}
