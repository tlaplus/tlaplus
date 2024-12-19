/*******************************************************************************
 * Copyright (c) 2024 Microsoft Research. All rights reserved.
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

import static org.junit.Assert.assertTrue;

import java.io.IOException;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.FileUtil;

public class Github858Test extends ModelCheckerTestCase {

	public Github858Test() {
		super("EWD998", "EWD998/",
				new String[] { "-config", "Github858.cfg", "-simulate", "-dumptrace", "tlcaction",
						"states" + FileUtil.separator + Github858Test.class.getCanonicalName() + ".tla" },
				EC.ExitStatus.VIOLATION_SAFETY);
	}

	@Override
	protected boolean noGenerateSpec() {
		return false;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Test
	public void testSpec() throws IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		assertState(recorder.getRecords(EC.TLC_STATE_PRINT2), 100,
				"/\\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE)\n"
						+ "/\\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)\n"
						+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\")\n"
						+ "/\\ counter = (0 :> -1 @@ 1 :> 0 @@ 2 :> 1)\n"
						+ "/\\ token = [pos |-> 1, q |-> 1, color |-> \"black\"]\n"
						+ "/\\ TokenInits = 4\n"
						+ "/\\ TokenPasses = 7\n" 
						+ "/\\ Activations = (0 :> 6 @@ 1 :> 7 @@ 2 :> 9)\n"
						+ "/\\ Activations2 = (0 :> 6 @@ 1 :> 7 @@ 2 :> 9)\n"
						+ "/\\ Actives = { (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE),\n"
						+ "  (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE),\n"
						+ "  (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE),\n"
						+ "  (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE),\n"
						+ "  (0 :> TRUE @@ 1 :> FALSE @@ 2 :> TRUE),\n"
						+ "  (0 :> TRUE @@ 1 :> TRUE @@ 2 :> FALSE),\n"
						+ "  (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE) }\n"
						+ "/\\ SumQ = 129\n"
						+ "/\\ SumQP = 130",
				"<PassToken(2) line 57, col 3 to line 64, col 43 of module EWD998>");
	}
}
