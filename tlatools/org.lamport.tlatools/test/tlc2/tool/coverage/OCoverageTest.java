/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corporation. All rights reserved. 
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
package tlc2.tool.coverage;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

/**
 * The expression that a module instantiation substitutes for a parameter is
 * counted once per root that evaluates it. The Subst belongs to the semantic
 * graph and is thus shared by the next-state relation and the invariant of
 * module O, but each of them has its own OpApplNodeWrapper for the x in WITH y
 * <- x.
 * <p>
 * Before the CostModel of a substitution moved from the Subst to the root, the
 * root created last owned it: the invariant reported the sum of both, 11, and
 * the next-state relation reported nothing for line 22.
 */
public class OCoverageTest extends AbstractCoverageTest {

	public OCoverageTest() {
		super("O");
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "4"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "4", "4", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		assertCoverage("<Init line 24, col 1 to line 24, col 4 of module O>: 1:1\n"
				+ "  line 24, col 9 to line 24, col 13 of module O: 1\n" +
				// The seven evaluations of x in WITH y <- x that generating successors
				// caused. The invariant's four are reported below, not here.
				"<I!Step line 22, col 1 to line 22, col 1 of module O>: 3:3\n"
				+ "  line 22, col 31 to line 22, col 31 of module O: 7\n"
				+ "  line 10, col 15 to line 10, col 19 of module O: 3\n"
				+ "  |line 10, col 15 to line 10, col 15 of module O: 4\n"
				+ "  line 11, col 15 to line 11, col 24 of module O: 3\n" +
				// The invariant was evaluated in all four states, and so was the x
				// substituted into it, which is why the two collapse into one line.
				"<Inv line 28, col 1 to line 28, col 3 of module O>\n"
				+ "  line 28, col 8 to line 28, col 14 of module O: 4");
	}
}
