/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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

import org.junit.Test;
import org.junit.experimental.categories.Category;
import org.junit.runner.RunWith;
import org.junit.runners.BlockJUnit4ClassRunner;
import tlc2.output.EC;
import tlc2.overrides.Evaluation;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;
import util.IndependentlyRunTest;
import util.UniqueString;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

@RunWith(BlockJUnit4ClassRunner.class)
public class EvaluatingValueTest extends ModelCheckerTestCase {

    public EvaluatingValueTest() {
        super("EvaluatingValueTest");
    }

    @Evaluation(definition = "A", module = "EvaluatingValueTest")
    public synchronized static Value action(final TLCState s1) {

        // Set value of x variable of successor state to 42.
        s1.bind(UniqueString.of("x"), IntValue.gen(42));

        return BoolValue.ValTrue;
    }

    @Category(IndependentlyRunTest.class)
    @Test
    public void testSpec() {
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        // Two states: x = 1 and x = 42 (see action method below).
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "3", "2", "0"));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "2"));

        assertFalse(recorder.recorded(EC.GENERAL));

        assertFalse(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
        assertFalse(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
    }
}
