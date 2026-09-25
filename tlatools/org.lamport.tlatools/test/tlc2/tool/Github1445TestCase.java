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

import java.util.stream.Stream;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Base class of the regression tests for
 * https://github.com/tlaplus/tlaplus/issues/1445
 *
 * To investigate the race, set a breakpoint that suspends threads (not the VM)
 * where a subclass says the workers evaluate the shared value, and step into
 * SetEnumValue#normalize.
 */
public abstract class Github1445TestCase extends ModelCheckerTestCase {

	public Github1445TestCase() {
		super("Github1445", ExitStatus.SUCCESS);
	}

	/**
	 * Checks Github1445.tla with the given config file (without the .cfg
	 * extension) and extra arguments.
	 */
	public Github1445TestCase(final String config, final String... extraArguments) {
		super("Github1445", Stream.concat(Stream.of("-config", config + ".cfg"), Stream.of(extraArguments))
				.toArray(String[]::new), ExitStatus.SUCCESS);
	}

	@Override
	protected void beforeSetUp() {
		// The race causes a bogus counterexample of a liveness property. TLC
		// re-evaluates the properties on the counterexample to name the violated one,
		// finds none, and fails the assertion in Liveness#findViolatedProperties.
		// LiveCheck then calls System.exit, which crashes the forked VM instead of
		// failing the test. The IsolatedTestCaseRunner loads TLC's classes with a
		// fresh class loader per test, so this precedes the loading of Liveness.
		getClass().getClassLoader().setClassAssertionStatus("tlc2.tool.liveness.Liveness", false);
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

	@Override
	protected int getNumberOfThreads() {
		// The race requires multiple workers.
		return 8;
	}

	/**
	 * Asserts that TLC finished without errors and, unless stats is empty, that it
	 * reported the given numbers of generated states, distinct states, and states
	 * left on the queue.
	 */
	protected void assertSuccess(final String... stats) {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		if (stats.length > 0) {
			assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, stats));
		}
	}
}
