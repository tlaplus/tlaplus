/*******************************************************************************
 * Copyright (c) 2026 Tomas Junnonen. All rights reserved.
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
 *   Tomas Junnonen - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;

public class DiffTraceAliasLassoTest extends DiffTraceTestCase {

	public DiffTraceAliasLassoTest() {
		super("DiffTraceAlias", new String[] { "-difftrace", "-config", "DiffTraceAliasLasso.cfg" },
				ExitStatus.VIOLATION_LIVENESS);
	}

	@Test
	public void testSpec() {
		// ab, which is not a variable, is listed only when it changes.
		testPrintStream.assertContains("State 2: <SetA line 6, col 9 to line 6, col 48 of module DiffTrace>\n"
				+ "/\\ a = 1\n/\\ ab = 1\n\n"
				+ "State 3: <SetB line 7, col 9 to line 7, col 57 of module DiffTrace>\n"
				+ "/\\ b = 1\n/\\ ab = 2\n\n"
				+ "State 4: <SetC line 8, col 9 to line 8, col 57 of module DiffTrace>\n"
				+ "/\\ c = 1\n\n"
				+ "State 5: <SetD line 9, col 9 to line 9, col 57 of module DiffTrace>\n"
				+ "/\\ d = 1\n\n"
				+ "State 6: Stuttering");
	}
}
