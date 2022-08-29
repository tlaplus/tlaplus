/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

import junit.framework.TestCase;
import org.junit.Test;
import tla2sany.semantic.OpDeclNode;
import tlc2.tool.queue.DummyTLCState;
import tlc2.util.SetOfStates;

import java.util.HashSet;
import java.util.Set;

public class SetOfStatesTest extends TestCase {

    @Test
    public void testSizeEmpty() {
        final SetOfStates s = new SetOfStates(16);

        assertEquals(16, s.capacity());
        assertEquals(0, s.size());
    }

    @Test
    public void testSize() {
        final SetOfStates s = new SetOfStates(16);
        s.add(new DummyTLCState(new OpDeclNode[]{}, 1L));

        assertEquals(16, s.capacity());
        assertEquals(1, s.size());
    }

    @Test
    public void testGrow() {
        final SetOfStates s = new SetOfStates(1);

        for (int i = 0; i < 32; i++) {
            s.add(new DummyTLCState(new OpDeclNode[]{}, i));
        }

        assertTrue(s.capacity() > 32);
        assertEquals(32, s.size());
    }

    @Test
    public void testIterate() {
        final SetOfStates s = new SetOfStates(1);

        for (int i = 1; i <= 32; i++) {
            assertFalse(s.add(new DummyTLCState(new OpDeclNode[]{}, i)));
        }
        assertEquals(32, s.size());

        // successor is not equal to predecessor
        TLCState predecessor = null;
        for (final TLCState state : s) {
            assertNotSame(predecessor, state);
            predecessor = state;
        }


        // The combined sum of elements is correct
        long sum = 0L;

        for (final TLCState elem : s) {
            sum += elem.fingerPrint();
        }
        assertEquals((32 / 2) * (1 + 32), sum);
    }

    @Test
    public void testDuplicates() {
        final SetOfStates s = new SetOfStates(1);

        for (int i = 1; i <= 32; i++) {
            assertFalse(s.add(new DummyTLCState(new OpDeclNode[]{}, i)));
        }
        assertEquals(32, s.size());

        // Adding the same elements again fails
        final Set<TLCState> states = new HashSet<>(s.size());
        var it = s.iterator();
        for (int i = 0; i < s.size(); i++) {
            states.add(it.next());
        }
        for (final TLCState aState : states) {
            assertTrue(s.add(aState));
        }
        assertEquals(32, states.size());
    }

    @Test
    public void testDuplicatesButNotEqual() {
        // duplicates in terms of fingerprints, but not in terms of equality
        // (symmetry).
        final SetOfStates s = new SetOfStates(1);

        int id = 1;
        for (int i = 1; i <= 32; i++) {
            assertFalse(s.add(new EqualityDummyTLCState(new OpDeclNode[]{}, i, id++)));
        }
        assertEquals(32, s.size());

        // Add 32 more elements with identical fp but different ids
        for (int i = 1; i <= 32; i++) {
            assertFalse(s.add(new EqualityDummyTLCState(new OpDeclNode[]{}, i, id++)));
        }
        assertEquals(64, s.size());

        // Add 32 more elements with identical fp and ids
        id = 1;
        for (int i = 1; i <= 32; i++) {
            assertTrue(s.add(new EqualityDummyTLCState(new OpDeclNode[]{}, i, id++)));
        }
        assertEquals(64, s.size());
    }

    @SuppressWarnings("serial")
    private static class EqualityDummyTLCState extends DummyTLCState {

        private final int id;

        public EqualityDummyTLCState(OpDeclNode[] vars, final int fp, final int id) {
            super(vars, fp);
            this.id = id;
        }

        /* (non-Javadoc)
         * @see java.lang.Object#hashCode()
         */
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + id;
            result = (int) (prime * result + fingerPrint());
            return result;
        }

        /* (non-Javadoc)
         * @see java.lang.Object#equals(java.lang.Object)
         */
        public boolean equals(final Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            final EqualityDummyTLCState other = (EqualityDummyTLCState) obj;
            if (fingerPrint() != other.fingerPrint())
                return false;
            return id == other.id;
        }
    }
}
