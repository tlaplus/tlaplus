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

import org.junit.Test;

import tlc2.output.EC;

/**
 * Regression test for https://github.com/tlaplus/tlaplus/issues/1445
 *
 * Liveness#astToLive binds the values of \E in the context of a state predicate
 * (LNStateAST) of a property's tableau. Workers race to normalize S when
 * LiveCheck#addNextState evaluates the predicate (LNStateAST#eval), which
 * drops elements from S and causes a bogus violation of the property.
 */
public class Github1445dTest extends Github1445TestCase {

	public Github1445dTest() {
		super("Github1445d");
	}

	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		// 8 initial states and 8 * 2048 successor states. Each of the latter also
		// generates itself by stuttering.
		assertSuccess("32776", "16392", "0");
	}
}
