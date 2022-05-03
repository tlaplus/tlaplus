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
package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github726Test extends ModelCheckerTestCase {

	private static final TestPrintWriter TEST_WRITER = new TestPrintWriter(System.out);

	public Github726Test() {
		super("Github726");
		tlc2.module.TLC.OUTPUT = TEST_WRITER;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "0"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "0", "0", "0"));
		
		assertTrue(TEST_WRITER.log.contains("[data |-> 15, dst |-> \"a\"]\n"));
		assertFalse(TEST_WRITER.log.contains("[data |-> \"a\", dst |-> 15]\n"));
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}
	
	private static class TestPrintWriter extends PrintWriter {

		public final List<String> log = new ArrayList<>();
		
		public TestPrintWriter(PrintStream out) {
			super(out);
		}

		@Override
		public void write(String x) {
			log.add(x);
			super.write(x);
		}
	}
}
