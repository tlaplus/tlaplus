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
package tlc2.value.impl;

import org.junit.Test;
import tlc2.util.FP64;
import tlc2.value.impl.SetOfFcnsValue.SubsetEnumerator;
import util.Assert.TLCRuntimeException;

import java.util.*;
import java.util.stream.IntStream;

import static org.junit.Assert.*;

public class SetOfFcnsValueTest {

    private static Value[] getValue(final String... strs) {
        final Value[] values = new Value[strs.length];
        for (int i = 0; i < strs.length; i++) {
            values[i] = new StringValue(strs[i]);
        }
        return values;
    }

    @Test
    public void testRangeSubsetValue() {
        final Value[] values = new Value[]{ModelValue.make("m1"), ModelValue.make("m2"), ModelValue.make("m3")};
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(new SetEnumValue(values, true),
                new SubsetValue(new SetEnumValue(
                        new Value[]{new StringValue("a"), new StringValue("b"), new StringValue("c")}, true)));

        assertEquals(512, setOfFcnsValue.size());

        final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(512);
        final SetEnumValue emptyset = new SetEnumValue();
        int i = 0;
        assertEquals(new FcnRcdValue(values, new Value[]{emptyset, emptyset, emptyset}, true),
                enumerator.get(i++));
        assertEquals(
                new FcnRcdValue(values,
                        new Value[]{emptyset, emptyset,
                                new SetEnumValue(new Value[]{new StringValue("a")}, true)},
                        true),
                enumerator.get(i++));
        assertEquals(
                new FcnRcdValue(values,
                        new Value[]{emptyset, emptyset,
                                new SetEnumValue(new Value[]{new StringValue("b")}, true)},
                        true),
                enumerator.get(i++));
        assertEquals(new FcnRcdValue(values,
                new Value[]{emptyset, emptyset,
                        new SetEnumValue(new Value[]{new StringValue("c")}, true)},
                true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(values,
                new Value[]{emptyset, emptyset,
                        new SetEnumValue(new Value[]{new StringValue("a"), new StringValue("b")}, true)},
                true), enumerator.get(i++));

        // Last element
        final SetEnumValue setEnumValue = new SetEnumValue(
                new Value[]{new StringValue("a"), new StringValue("b"), new StringValue("c")}, true);
        assertEquals(new FcnRcdValue(values, new Value[]{setEnumValue, setEnumValue, setEnumValue}, true),
                enumerator.get(511));
    }

    @Test
    public void testDomainEmpty() {
        final SetEnumValue domain = new SetEnumValue();
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain,
                new SetEnumValue(getValue("a", "b", "c"), true));

        // Non-subset behavior is our prototype.
        assertEquals(1, setOfFcnsValue.size());
        final ValueEnumeration elements = setOfFcnsValue.elements();
        assertEquals(new FcnRcdValue(new Value[0], new Value[0], true), elements.nextElement());
        assertNull(elements.nextElement());

        // Subset behaves similar.
        final Enumerable subset = setOfFcnsValue.getRandomSubset(5);
        final ValueEnumeration subsetElements = subset.elements();
        assertEquals(1, subset.size());
        assertEquals(new FcnRcdValue(new Value[0], new Value[0], true), subsetElements.nextElement());
        assertNull(subsetElements.nextElement());
    }

    @Test
    public void testRangeEmpty() {
        final IntervalValue domain = new IntervalValue(1, 2);
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain, new SetEnumValue(new ValueVec(), true));

        // Non-subset behavior is our prototype.
        assertEquals(0, setOfFcnsValue.size());
        assertNull(setOfFcnsValue.elements().nextElement());

        // Subset behaves similar.
        final Enumerable subset = setOfFcnsValue.getRandomSubset(5);
        assertEquals(0, subset.size());
        assertNull(subset.elements().nextElement());
        assertEquals(new SetEnumValue(), subset);
    }

    @Test
    public void testDomainAndRangeEmpty() {
        final SetEnumValue domain = new SetEnumValue();
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain, new SetEnumValue());

        // Non-subset behavior is our prototype.
        assertEquals(1, setOfFcnsValue.size());
        final ValueEnumeration elements = setOfFcnsValue.elements();
        assertEquals(new FcnRcdValue(new Value[0], new Value[0], true), elements.nextElement());
        assertNull(elements.nextElement());

        // Subset behaves similar.
        final Enumerable subset = setOfFcnsValue.getRandomSubset(5);
        final ValueEnumeration subsetElements = subset.elements();
        assertEquals(1, subset.size());
        assertEquals(new FcnRcdValue(new Value[0], new Value[0], true), subsetElements.nextElement());
        assertNull(subsetElements.nextElement());
    }

    @Test
    public void testRandomSubsetAndValueEnumerator() {
        final Value[] domain = new Value[]{ModelValue.make("m1"), ModelValue.make("m2"), ModelValue.make("m3")};
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(new SetEnumValue(domain, true),
                new SetEnumValue(getValue("a", "b", "c"), true));

        assertEquals(27, setOfFcnsValue.size());

        FP64.Init();
        final Set<FcnRcdValue> enumeratorValues = new HashSet<>(27);

        final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(27);
        for (int i = 0; i < setOfFcnsValue.size(); i++) {
            final FcnRcdValue rcd = (FcnRcdValue) enumerator.get(i);
            assertEquals(3, Objects.requireNonNull(rcd.domain).length);
            assertEquals(3, rcd.values.length);
            enumeratorValues.add(rcd);
        }

        final Enumerable randomSubset = setOfFcnsValue.getRandomSubset(27);
        final Set<FcnRcdValue> randomsubsetValues = new HashSet<>(27);

        final ValueEnumeration enumerator2 = randomSubset.elements();
        FcnRcdValue rcd;
        while ((rcd = (FcnRcdValue) enumerator2.nextElement()) != null) {
            assertEquals(3, Objects.requireNonNull(rcd.domain).length);
            assertEquals(3, rcd.values.length);
            randomsubsetValues.add(rcd);
            // Check element is in the original SetOfFcnsValue.
            assertTrue(setOfFcnsValue.member(rcd));
        }

        assertEquals(enumeratorValues.size(), randomsubsetValues.size());
        assertEquals(enumeratorValues, randomsubsetValues);
    }

    @Test
    public void testDomainModelValue() {
        final Value[] domain = new Value[]{ModelValue.make("m1"), ModelValue.make("m2"), ModelValue.make("m3")};
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(new SetEnumValue(domain, true),
                new SetEnumValue(getValue("a", "b", "c"), true));

        assertEquals(27, setOfFcnsValue.size());

        FP64.Init();
        final Set<FcnRcdValue> enumeratorValues = new HashSet<>(27);

        final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(27);
        for (int i = 0; i < setOfFcnsValue.size(); i++) {
            final FcnRcdValue rcd = (FcnRcdValue) enumerator.get(i);
            assertEquals(3, Objects.requireNonNull(rcd.domain).length);
            assertEquals(3, rcd.values.length);
            enumeratorValues.add(rcd);
            // Check element is in the original SetOfFcnsValue.
            assertTrue(setOfFcnsValue.member(rcd));
        }
        assertEquals(27, enumeratorValues.size());

        int i = 0;
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "c"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "b", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "b", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "b", "c"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "c", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "c", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "c", "c"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "a", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "a", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "a", "c"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "b", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "b", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "b", "c"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "c", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "c", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "c", "c"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "a", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "a", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "a", "c"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "b", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "b", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "b", "c"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "c", "a"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "c", "b"), true), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "c", "c"), true), enumerator.get(i++));
    }

    @Test
    public void testDomainIntervalRangeSetEnumValueSize9() {
        final IntervalValue domain = new IntervalValue(1, 2);
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain,
                new SetEnumValue(getValue("a", "b", "c"), true));

        assertEquals(9, setOfFcnsValue.size());

        final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(9);
        for (int i = 0; i < setOfFcnsValue.size(); i++) {
            final FcnRcdValue rcd = (FcnRcdValue) enumerator.get(i);
            assertEquals(2, Objects.requireNonNull(rcd.domain).length);
            assertEquals(2, rcd.values.length);
            // Check element is in the original SetOfFcnsValue.
            assertTrue(setOfFcnsValue.member(rcd));
        }

        int i = 0;
        assertEquals(new FcnRcdValue(domain, getValue("a", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "c")), enumerator.get(i++));
    }

    @Test
    public void testDomainIntervalRangeSetEnumValueSize27() {
        final IntervalValue domain = new IntervalValue(1, 3);
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain,
                new SetEnumValue(getValue("a", "b", "c"), true));

        assertEquals(27, setOfFcnsValue.size());

        final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(27);
        for (int i = 0; i < setOfFcnsValue.size(); i++) {
            final FcnRcdValue rcd = (FcnRcdValue) enumerator.get(i);
            assertEquals(3, Objects.requireNonNull(rcd.domain).length);
            assertEquals(3, rcd.values.length);
            // Check element is in the original SetOfFcnsValue.
            assertTrue(setOfFcnsValue.member(rcd));
        }

        int i = 0;
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "b", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "b", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "b", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "c", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "c", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "c", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "a", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "a", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "a", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "b", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "b", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "b", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "c", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "c", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("b", "c", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "a", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "a", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "a", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "b", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "b", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "b", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "c", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "c", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("c", "c", "c")), enumerator.get(i++));
    }

    @Test
    public void testDomainIntervalRangeSetEnumValueSize256() {
        final IntervalValue domain = new IntervalValue(1, 4);
        final SetOfFcnsValue setOfFcnsValue = new SetOfFcnsValue(domain,
                new SetEnumValue(getValue("a", "b", "c", "d"), true));

        assertEquals(256, setOfFcnsValue.size());

        final SetOfFcnsValue.SubsetEnumerator enumerator = (SubsetEnumerator) setOfFcnsValue.elements(256);
        for (int i = 0; i < setOfFcnsValue.size(); i++) {
            final FcnRcdValue rcd = (FcnRcdValue) enumerator.get(i);
            assertEquals(4, Objects.requireNonNull(rcd.domain).length);
            assertEquals(4, rcd.values.length);
            // Check element is in the original SetOfFcnsValue.
            assertTrue(setOfFcnsValue.member(rcd));
        }

        int i = 0;
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a", "a")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a", "b")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a", "c")), enumerator.get(i++));
        assertEquals(new FcnRcdValue(domain, getValue("a", "a", "a", "d")), enumerator.get(i++));
        // ... (to lazy to type them out)
        assertEquals(new FcnRcdValue(domain, getValue("d", "d", "d", "b")), enumerator.get(253));
        assertEquals(new FcnRcdValue(domain, getValue("d", "d", "d", "c")), enumerator.get(254));
        assertEquals(new FcnRcdValue(domain, getValue("d", "d", "d", "d")), enumerator.get(255));
    }

    @Test
    public void testRandomSubsetFromReallyLarge() {
        final List<SetOfFcnsValue> l = new ArrayList<>();

        l.add(new SetOfFcnsValue(new IntervalValue(1, 11),
                new SetEnumValue(getValue("a", "b", "c", "d", "e", "f", "g", "h", "i", "j"), true)));
        l.add(new SetOfFcnsValue(new IntervalValue(1, 44), new IntervalValue(1, 20)));
        l.add(new SetOfFcnsValue(new IntervalValue(1, 121), new IntervalValue(1, 19)));
        l.add(new SetOfFcnsValue(new IntervalValue(1, 321), new IntervalValue(1, 29)));

        l.forEach(sofv -> {
            try {
                sofv.size();
            } catch (final TLCRuntimeException tre) {
                // OK, set is huge for size to reject it. Next get a tiny subset of it.

                // 109031 causes the test to take a little long to be included in the overall test suite.
                IntStream.of(0, 1, 2, 799, 1024, 8932, 16933/*, 109031*/).forEach(kOutOfN -> {
                    final Enumerable randomSubset = sofv.getRandomSubset(kOutOfN);

                    // Check expected amount of elements.
                    assertEquals(kOutOfN, randomSubset.size());

                    // Check for no duplicates.
                    FP64.Init();
                    final Set<FcnRcdValue> set = new HashSet<>(kOutOfN);

                    final ValueEnumeration elements = randomSubset.elements();
                    FcnRcdValue rcd;
                    while ((rcd = (FcnRcdValue) elements.nextElement()) != null) {
                        // Check element is in the original SetOfFcnsValue.
                        assertTrue(sofv.member(rcd));
                        set.add(rcd);
                    }
                    assertEquals(kOutOfN, set.size());
                });
                return;
            }
            fail();
        });
    }
}
