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
package tlc2.tool.coverage;

import tla2sany.semantic.SemanticNode;

public interface CostModel {

	CostModel DO_NOT_RECORD = new CostModel() {

		@Override
		public final CostModel report() {
			// no-op
			return this;
		}

		@Override
		public final CostModel get(final SemanticNode sn) {
			return this;
		}
		
		@Override
		public final CostModel getRoot() {
			return this;
		}

		@Override
		public final CostModel incInvocations() {
			// no-op
			return this;
		}

		@Override
		public final CostModel incInvocations(final long value) {
			// no-op
			return this;
		}

		@Override
		public final CostModel incSecondary() {
			// no-op
			return this;
		}

		@Override
		public final CostModel incSecondary(long value) {
			// no-op
			return null;
		}

		@Override
		public final CostModel getAndIncrement(SemanticNode eon) {
			// no-op
			return this;
		}
		
		@Override
		public final String toString() {
			return "DO_NOT_RECORD";
		}
	};

	CostModel incInvocations();

	CostModel incInvocations(final long value);

	CostModel incSecondary();
	
	CostModel incSecondary(final long value);

	CostModel report();

	CostModel get(final SemanticNode sn);
	
	CostModel getAndIncrement(final SemanticNode eon);
	
	CostModel getRoot();
}
