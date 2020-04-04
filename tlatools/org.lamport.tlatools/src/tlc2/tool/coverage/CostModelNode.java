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

import java.util.LinkedHashMap;
import java.util.Map;

import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.TLCGlobals;
import tlc2.util.statistics.CounterStatistic;

public abstract class CostModelNode implements CostModel {
	
	// children has to preserve order to later traverse tree in the module location
	// order when reporting coverage. Thus, use LinkedHashMap here.
	protected final Map<SemanticNode, CostModelNode> children = new LinkedHashMap<>();

	protected final CounterStatistic stats = CounterStatistic.getInstance(() -> TLCGlobals.isCoverageEnabled());
	protected final CounterStatistic secondary = CounterStatistic.getInstance(() -> TLCGlobals.isCoverageEnabled());
	
	// ---------------- Statistics ---------------- //

	protected long getEvalCount() {
		return this.stats.getCount();
	}

	protected long getSecondary() {
		return this.secondary.getCount();
	}

	protected abstract Location getLocation();

	// -- --//
	
	void addChild(final CostModelNode child) {
		final boolean newlyInserted = this.children.put(child.getNode(), child) == null;
		assert newlyInserted;
	}

	abstract SemanticNode getNode();
	
	@Override
	public abstract CostModelNode getRoot();
	
	boolean isRoot() {
		return false;
	}

	int getLevel() {
		return 0;
	}
	
	// -- -- //
	
	@Override
	public final CostModel getAndIncrement(final SemanticNode eon) {
		return get(eon).incInvocations();
	}

	@Override
	public final CostModel incInvocations(long size) {
		this.stats.add(size);
		return this;
	}

	@Override
	public final CostModel incInvocations() {
		this.stats.increment();
		return this;
	}

	public final CostModel incSecondary() {
		this.secondary.increment();
		return this;
	}

	@Override
	public final CostModel incSecondary(final long value) {
		this.secondary.add(value);
		return this;
	}
}
