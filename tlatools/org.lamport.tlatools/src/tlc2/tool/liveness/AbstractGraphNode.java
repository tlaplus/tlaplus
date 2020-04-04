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

package tlc2.tool.liveness;

import tlc2.util.BitVector;

public abstract class AbstractGraphNode {

	protected BitVector checks; // truth values for state and action predicates

	public AbstractGraphNode(BitVector bitVector) {
		checks = bitVector;
	}

	public boolean getCheckState(int i) {
		return this.checks.get(i);
	}

	public BitVector getCheckAction(int slen, int alen, int nodeIdx) {
		final BitVector bv = new BitVector(alen);
		for (int j = 0; j < alen; j++) {
			bv.set(j, getCheckAction(slen, alen, nodeIdx, j));
		}
		return bv;
	}

	public boolean getCheckAction(int slen, int alen, int nodeIdx, int i) {
		int pos = slen + alen * nodeIdx + i;
		return this.checks.get(pos);
	}

	public boolean getCheckAction(int slen, int alen, int nodeIdx, int[] is) {
		int len = is.length;
		for (int i = 0; i < len; i++) {
			int pos = slen + alen * nodeIdx + is[i];
			if (!this.checks.get(pos)) {
				return false;
			}
		}
		return true;
	}

	public void setCheckState(boolean[] vals) {
		int len = vals.length;
		for (int i = 0; i < len; i++) {
			if (vals[i]) {
				this.checks.set(i);
			}
		}
	}
}
