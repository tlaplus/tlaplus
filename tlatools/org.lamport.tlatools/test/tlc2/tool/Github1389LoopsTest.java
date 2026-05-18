/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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

import java.io.IOException;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Regression test for https://github.com/tlaplus/tlaplus/issues/1389 and the
 * related stack overflow described in
 * https://github.com/tlaplus/tlaplus/issues/720.
 *
 * Exercises a RECURSIVE operator whose body is at temporal level and whose
 * recursion does not terminate during tableau construction. The liveness
 * translator expands the operator until the JVM raises a
 * {@link StackOverflowError}, which TLC's top-level catch in
 * {@code TLC.process} translates into {@link EC#SYSTEM_STACK_OVERFLOW}. This
 * matches how the rest of the codebase reports non-terminating recursion (e.g.
 * {@link tlc2.tool.ModelChecker} init/doNext,
 * {@link tlc2.tool.DFIDModelChecker}, {@link tlc2.tool.liveness.LiveCheck}).
 */
public class Github1389LoopsTest extends ModelCheckerTestCase {

	public Github1389LoopsTest() {
		super("Github1389Loops", EC.ExitStatus.ERROR);
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Test
	public void testSpec() throws IOException {
		assertTrue(recorder.recorded(EC.SYSTEM_STACK_OVERFLOW));
		// EC.GENERAL records unexpected internal errors; SOE must be
		// classified specifically as SYSTEM_STACK_OVERFLOW, not as the
		// generic-error catch-all.
		assertFalse(recorder.recorded(EC.GENERAL));
	}
}
