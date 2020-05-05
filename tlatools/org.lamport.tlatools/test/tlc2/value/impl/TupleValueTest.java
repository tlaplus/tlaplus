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
 ******************************************************************************/
package tlc2.value.impl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SetOfTuplesValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.Assert;


public class TupleValueTest {

    @Test
    public void testErrorMessages() {
        Value elems[] = {new StringValue("A")};
        final TupleValue tupVal = new TupleValue(elems);

        try{
            tupVal.apply(IntValue.gen(2), 0);
        } catch(Assert.TLCRuntimeException ex){
            assertTrue(ex.getMessage().contains("Attempted to access index 2 of tuple\n<<\"A\">>\nwhich is out of bounds"));
        }

        try{
            tupVal.apply(new StringValue("a"), 0);
        } catch(Assert.TLCRuntimeException ex){
            assertTrue(ex.getMessage().contains("Attempted to access tuple at a non integral index: \"a\""));
        }

        try{
            tupVal.select(new StringValue("a"));
        } catch(Assert.TLCRuntimeException ex){
            assertTrue(ex.getMessage().contains("Attempted to access tuple at a non integral index: \"a\""));
        }

        try{
            Value args[] = {new StringValue("arg1"), new StringValue("arg2")};
            tupVal.apply(args, 0);
        } catch(Assert.TLCRuntimeException ex){
            assertTrue(ex.getMessage().contains("Attempted to access tuple with 2 arguments when it expects 1."));
        }
    }
}
