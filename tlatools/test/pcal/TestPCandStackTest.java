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
package pcal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class TestPCandStackTest extends PCalModelCheckerTestCase {

	public TestPCandStackTest() {
		super("TestPCandStack", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
	}
}
/*
TLC2 Version 2.12 of 29 January 2018
Running breadth-first search Model-Checking with 1 worker on 4 cores with 5303MB heap and 64MB offheap memory (Linux 4.15.0-22-generic amd64, Oracle Corporation 1.8.0_171 x86_64).
Parsing file /home/markus/Desktop/LesliePCalTest/alltests/TestPCandStack.tla
Parsing file /home/markus/src/TLA/tla/tlatools/class/tla2sany/StandardModules/Naturals.tla
Parsing file /home/markus/src/TLA/tla/tlatools/class/tla2sany/StandardModules/Sequences.tla
Parsing file /home/markus/src/TLA/tla/tlatools/class/tla2sany/StandardModules/TLC.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module TLC
Semantic processing of module TestPCandStack
Starting... (2018-05-23 12:30:30)
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Warning: The EXCEPT was applied to non-existing fields of the value at
line 46, col 26 to line 46, col 30 of module TestPCandStack
(Use the -nowarning option to disable this warning.)
Error: TLC threw an unexpected exception.
This was probably caused by an error in the spec or model.
See the User Output or TLC Console for clues to what happened.
The exception was a tlc2.tool.EvalException
: Attempted to apply the operator overridden by the Java method
public static tlc2.value.Value tlc2.module.TLC.Assert(tlc2.value.Value,tlc2.value.Value),
but it produced the following error:
The first argument of Assert evaluated to FALSE; the second argument was:
"Failure of assertion at line 16, column 26."
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ stack = <<<<>>, <<>>, <<>>>>
/\ pc = <<"M1", "M1", "M1">>

State 2: <M1 line 43, col 13 to line 47, col 47 of module TestPCandStack>
/\ stack = <<<<>>, <<>>, <<>>>>
/\ pc = <<"M2", "M1", "M1">>

Error: The error occurred when TLC was evaluating the nested
expressions at the following positions:
0. Line 49, column 13 to line 56, column 29 in TestPCandStack
1. Line 49, column 16 to line 49, column 30 in TestPCandStack
2. Line 50, column 16 to line 54, column 79 in TestPCandStack
3. Line 51, column 24 to line 52, column 79 in TestPCandStack
4. Line 51, column 27 to line 52, column 79 in TestPCandStack


4 states generated, 4 distinct states found, 2 states left on queue.
The depth of the complete state graph search is 2.
The average outdegree of the complete state graph is 3 (minimum is 3, the maximum 3 and the 95th percentile is 3).
Finished in 00s at (2018-05-23 12:30:30)
*/