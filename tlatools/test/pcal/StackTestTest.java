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

public class StackTestTest extends PCalModelCheckerTestCase {

	public StackTestTest() {
		super("StackTest", "pcal");
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
Parsing file /home/markus/Desktop/LesliePCalTest/alltests/StackTest.tla
Parsing file /home/markus/src/TLA/tla/tlatools/class/tla2sany/StandardModules/Sequences.tla
Parsing file /home/markus/src/TLA/tla/tlatools/class/tla2sany/StandardModules/Naturals.tla
Parsing file /home/markus/src/TLA/tla/tlatools/class/tla2sany/StandardModules/TLC.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module TLC
Semantic processing of module StackTest
Starting... (2018-05-23 12:30:31)
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Warning: The EXCEPT was applied to non-existing fields of the value at
line 36, col 26 to line 36, col 30 of module StackTest
(Use the -nowarning option to disable this warning.)
Error: TLC threw an unexpected exception.
This was probably caused by an error in the spec or model.
See the User Output or TLC Console for clues to what happened.
The exception was a tlc2.tool.EvalException
: Attempted to apply the operator overridden by the Java method
public static tlc2.value.Value tlc2.module.TLC.Assert(tlc2.value.Value,tlc2.value.Value),
but it produced the following error:
The first argument of Assert evaluated to FALSE; the second argument was:
"Failure of assertion at line 13, column 17."
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ stack = (0 :> <<>> @@ 1 :> <<>> @@ 2 :> <<>>)
/\ a = (0 :> 42 @@ 1 :> 42 @@ 2 :> 42)
/\ pc = (0 :> "Q1" @@ 1 :> "Q1" @@ 2 :> "Q1")

State 2: <Q1 line 51, col 13 to line 59, col 47 of module StackTest>
/\ stack = ( 0 :> <<[pc |-> "Done", a |-> 42, procedure |-> "P"]>> @@
  1 :> <<>> @@
  2 :> <<>> )
/\ a = (0 :> 22 @@ 1 :> 42 @@ 2 :> 42)
/\ pc = (0 :> "P1" @@ 1 :> "Q1" @@ 2 :> "Q1")

Error: The error occurred when TLC was evaluating the nested
expressions at the following positions:
0. Line 35, column 13 to line 42, column 21 in StackTest
1. Line 35, column 16 to line 35, column 30 in StackTest
2. Line 36, column 16 to line 36, column 80 in StackTest
3. Line 37, column 16 to line 38, column 68 in StackTest


4 states generated, 4 distinct states found, 2 states left on queue.
The depth of the complete state graph search is 2.
The average outdegree of the complete state graph is 3 (minimum is 3, the maximum 3 and the 95th percentile is 3).
Finished in 00s at (2018-05-23 12:30:31)
*/