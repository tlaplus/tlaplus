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
package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.*;

public class Randomization implements ValueConstants {

    public static final long serialVersionUID = 20180618L;

    public static Value RandomSubset(final Value v1, final Value v2) {
        if (v1 instanceof IntValue v1IV) {
            if (v2 instanceof EnumerableValue v2EV && v2.isFinite()) {
                return v2EV.getRandomSubset(v1IV.val);
            } else {
                // v2 has to be enumerable (infinite sets are not enumerable and impossible to draw from uniformly anyway).
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                        new String[]{"second", "RandomSubset", "a finite set", Values.ppr(v2.toString())});
            }
        } else {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"first", "RandomSubset", "nonnegative integer", Values.ppr(v1.toString())});
        }
    }

    public static Value RandomSetOfSubsets(final Value v1, final Value v2, final Value v3) {
        // first parameter
        if (!(v1 instanceof IntValue)) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"first", "RandomSetOfSubsets", "nonnegative integer", Values.ppr(v1.toString())});
        }
        final int numberOfPicks = ((IntValue) v1).val;
        if (numberOfPicks < 0) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"first", "RandomSetOfSubsets", "nonnegative integer", Values.ppr(v1.toString())});
        }
        // second parameter
        if (!(v2 instanceof IntValue)) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"second", "RandomSetOfSubsets", "nonnegative integer", Values.ppr(v2.toString())});
        }
        final int n = ((IntValue) v2).val;
        if (n < 0) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"second", "RandomSetOfSubsets", "nonnegative integer", Values.ppr(v2.toString())});
        }
        // third parameter
        if (!(v3 instanceof final EnumerableValue ev) || !v3.isFinite()) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"third", "RandomSetOfSubsets", "finite set", Values.ppr(v3.toString())});
        }
        if (31 - Integer.numberOfLeadingZeros(numberOfPicks) + 1 > ev.size() && numberOfPicks > (1 << ev.size())) {
            // First compare exponents before explicit calculating size of subset. The
            // calculated value which is the subset's size then won't overflow.
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"first", "RandomSetOfSubsets",
                            "nonnegative integer that is smaller than the subset's size of 2^" + ev.size(),
                            Integer.toString(numberOfPicks)});
        }
        // second parameter (now that we know third is enumerable)
        if (ev.size() < n) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"second", "RandomSetOfSubsets", "nonnegative integer in range 0..Cardinality(S)", Values.ppr(v2.toString())});
        }
        final double probability = (1d * n) / ev.size();
        if (probability < 0d || 1d < probability) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"second", "RandomSetOfSubsets", "nonnegative integer in range 0..Cardinality(S)", Values.ppr(v2.toString())});
        }
        return new SubsetValue(ev).getRandomSetOfSubsets(numberOfPicks, probability);
    }

    public static Value RandomSubsetSet(final Value v1, final Value v2, final Value v3) {
        // first parameter
        if (!(v1 instanceof IntValue)) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"first", "RandomSubsetSetProbability", "nonnegative integer", Values.ppr(v1.toString())});
        }
        final int numberOfPicks = ((IntValue) v1).val;
        if (numberOfPicks < 0) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"first", "RandomSubsetSetProbability", "nonnegative integer", Values.ppr(v1.toString())});
        }
        // second parameter
        if (!(v2 instanceof StringValue)) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"second", "RandomSubsetSetProbability", "string literal representing a probability", Values.ppr(v2.toString())});

        }
        final double probability;
        try {
            probability = Double.parseDouble(((StringValue) v2).getVal().toString());
        } catch (final NumberFormatException nfe) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"second", "RandomSubsetSetProbability", "string literal does not represent a parsable probability", Values.ppr(v2.toString())});
        }
        if (probability < 0d || 1d < probability) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"second", "RandomSubsetSetProbability", "string literal does not represent a parsable probability", Values.ppr(v2.toString())});
        }
        // third parameter
        if (!(v3 instanceof final EnumerableValue ev) || !v3.isFinite()) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"third", "RandomSubsetSetProbability", "finite set", Values.ppr(v3.toString())});
        }
        if (31 - Integer.numberOfLeadingZeros(numberOfPicks) + 1 > ev.size() && numberOfPicks > (1 << ev.size())) {
            // First compare exponents before explicit calculating size of subset. The
            // calculated value which is the subset's size then won't overflow.
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR,
                    new String[]{"first", "RandomSubsetSetProbability",
                            "nonnegative integer that is smaller than the subset's size of 2^" + ev.size(),
                            Integer.toString(numberOfPicks)});
        }

        return new SubsetValue(ev).getRandomSetOfSubsets(numberOfPicks, probability);
    }
}
