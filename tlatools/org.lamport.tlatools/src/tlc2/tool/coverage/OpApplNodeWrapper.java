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

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;

public class OpApplNodeWrapper extends CostModelNode implements Comparable<OpApplNodeWrapper>, CostModel {

	private final Set<Pair> childCounts = new HashSet<>();
	private final CostModelNode root;
	private final OpApplNode node;
	// Periodic coverage reporting executes concurrently with the evaluation of the
	// init and next-state relation. Traversing the CostModel trees to collect the
	// individual eval counts creates thus an inconsistent snapshot. To reduce the
	// inconsistency, freeze the eval count for all tree nodes on the first tree
	// traversal while the child counts are calculated. The snapshot is still
	// inconsistent from the perspective of the evaluation, but at least the
	// reporting in print (eval counts reported to parent - childCounts - and eval
	// counts printed is consistent. Alternatively, evaluation of init and next
	// could be suspended for the duration of the snapshot, but that seems overkill.
	private long snapshotEvalCount = 0;
	private long snapshotSecondCount = 0;
	private boolean primed = false;
	private int level;
	private CostModelNode recursive;
	protected final Map<SemanticNode, CostModelNode> lets = new LinkedHashMap<>();

	OpApplNodeWrapper(OpApplNode node, CostModelNode root) {
		super();
		this.node = node;
		this.root = root;
		this.level = 0;
	}

	// For unit testing only.
	OpApplNodeWrapper() {
		this(null, null);
	}

	// For unit testing only.
	OpApplNodeWrapper(OpApplNode node, long samples) {
		this(node, null);
		this.incInvocations(samples);
	}

	// ---------------- Identity... ---------------- //
	
	@Override
	public int compareTo(OpApplNodeWrapper arg0) {
		return this.getLocation().compareTo(arg0.getLocation());
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((node.getLocation() == null) ? 0 : node.getLocation().hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		OpApplNodeWrapper other = (OpApplNodeWrapper) obj;
		if (node.getLocation() == null) {
			if (other.node.getLocation() != null)
				return false;
		} else if (!node.getLocation().equals(other.node.getLocation())) {
			return false;
		}
		return true;

	}

	@Override
	public String toString() {
		if (this.node == null) {
			return "root";
		}
		return node.toString();
	}
	
	// ----------------  ---------------- //

	@Override
	protected Location getLocation() {
		return this.node != null ? this.node.getLocation() : Location.nullLoc;
	}

	public OpApplNode getNode() {
		return this.node;
	}
	
	public boolean isRoot() {
		return this.node == null;
	}

	// ---------------- Parent <> Child ---------------- //
	
	public OpApplNodeWrapper addLets(OpApplNodeWrapper lets) {
		this.lets.put(lets.getNode(), lets);
		return this;
	}

	public OpApplNodeWrapper setRecursive(CostModelNode recursive) {
		assert this.recursive == null;
		this.recursive = recursive;
		return this;
	}
	
	@Override
	public CostModelNode getRoot() {
		assert this.root instanceof ActionWrapper;
		return this.root;
	}
	
	private final Set<Integer> seen = new HashSet<>();
	
	@Override
	public final CostModelNode get(final SemanticNode eon) {
		if (eon == this.node || !(eon instanceof OpApplNode)) {
			return this;
		}
		
		CostModelNode child = children.get(eon);
		if (child != null) {
			return child;
		}
		
		if (recursive != null) {
			child = recursive.children.get(eon);
			if (child != null) {
				return child;
			}
		}
		
		if (lets != null) {
			child = lets.get(eon);
			if (child != null) {
				return child;
			}
		}
		
		// TODO Not all places in Tool lookup the correct CM yet. This should only be an
		// engineering effort though.
		if (seen.add(eon.myUID)) {
			//...only report it once to not spam the Toolbox console.
			MP.printMessage(EC.TLC_COVERAGE_MISMATCH, new String[] { eon.toString(), this.toString() });
		}
		return this;
	}

	// ---------------- Level ---------------- //

	public int getLevel() {
		return this.level;
	}

	public OpApplNodeWrapper setLevel(int level) {
		this.level = level;
		return this;
	}

	// ---------------- Primed ---------------- //
	
	public OpApplNodeWrapper setPrimed() {
		assert !isPrimed();
		this.primed = true;
		return this;
	}

	protected boolean isPrimed() {
		return this.primed;
	}
	
	// ---------------- Print ---------------- //

	protected long getEvalCount(Calculate fresh) {
		if (fresh == Calculate.FRESH) {
			return super.getEvalCount();
		} else {
			return snapshotEvalCount;
		}
	}

	protected long getSecondCount(Calculate fresh) {
		if (fresh == Calculate.FRESH) {
			return super.getSecondary();
		} else {
			return snapshotSecondCount;
		}
	}

	public CostModel report() {
		print(0, Calculate.FRESH);
		return this;
	}

	protected void print(int level, final Calculate fresh) {
		final Set<Pair> collectedEvalCounts = new HashSet<>();
		this.collectChildren(collectedEvalCounts, fresh);
		if (collectedEvalCounts.isEmpty()) {
			// Subtree has nothing to report.
			if (getEvalCount(fresh) == 0l && !isPrimed()) {
				// ..this node neither (eval count zero => secondary zero).
				return;
			} else {
				printSelf(level++);
				return; // Do not invoke printSelf(...) again below.
			}
		}
		final Pair node = new Pair(getEvalCount(fresh), getSecondCount(fresh));

		if (collectedEvalCounts.size() == 1) {
			// The eval and secondary count of all children is consistent. We can, thus,
			// collapse subtrees into this node under the following cases.
			final Pair consistentChildren = getCount(collectedEvalCounts);

			if (consistentChildren.primary < node.primary || consistentChildren.secondary < consistentChildren.secondary) {
				// Cannot collapse subtree because inconsistent with this node.
				printSelf(level++);
				printChildren(level);
				return;
			}
			if (!isPrimed() && node.isZero() && consistentChildren.isNonZero()) {
				// Collapse consistent subtree into this node unless this node is primed.
				if (consistentChildren.secondary == 0l) {
					printSelf(level++, consistentChildren.primary);
				} else {
					printSelf(level++, consistentChildren.primary, consistentChildren.secondary);
				}
				return;
			}
			if (node.isZero() && consistentChildren.isZero()) {
				if (isPrimed()) {
					printSelf(level++);
				}
				// Have a primed in subtree.
				printChildren(level);
				return;
			}
			if (node.equals(consistentChildren)) {
				// Have a primed in subtree.
				printSelf(level++);
				return;
			}
		}

		// Subtree is inconsistent and needs to report itself.
		if (node.isNonZero() || isPrimed()) {
			printSelf(level++);
		}
		printChildren(level);
	}

	private Pair getCount(Set<Pair> collectWeights) {
		assert collectWeights.size() == 1;
		for (Pair l : collectWeights) {
			return l;
		}
		return null; // make compiler happy
	}
	
	protected void printChildren(final int level) {
		for (CostModelNode cmn : children.values()) {
			((OpApplNodeWrapper) cmn).print(level, Calculate.CACHED);
		}
	}

	protected void printSelf(final int level, final long count) {
		MP.printMessage(EC.TLC_COVERAGE_VALUE, new String[] {
				indentBegin(level, TLCGlobals.coverageIndent, getLocation().toString()), String.valueOf(count) });
	}
	
	protected void printSelf(final int level, final long count, final long cost) {
		MP.printMessage(EC.TLC_COVERAGE_VALUE_COST,
				new String[] { indentBegin(level, TLCGlobals.coverageIndent, getLocation().toString()),
						String.valueOf(count), String.valueOf(cost) });
	}

	protected void printSelf(final int level) {
		if (getSecondary() > 0) {
			printSelf(level, getEvalCount(), getSecondary());
		} else {
			printSelf(level, getEvalCount());
		}
	}

	protected static String indentBegin(final int n, final char c, final String str) {
		assert n >= 0;
		final String whitespaces = new String(new char[n]).replace('\0', c);
		return whitespaces + str;
	}
	
	static class Pair {
		public final long primary;
		public final long secondary;

		public Pair(long primary, long secondary) {
			this.primary = primary;
			this.secondary = secondary;
		}
		public boolean isZero() {
			return primary == 0 && secondary == 0;
		}

		public boolean isNonZero() {
			return primary > 0 || secondary > 0;
		}

		@Override
		public int hashCode() {
			return Objects.hash(primary, secondary);
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			Pair other = (Pair) obj;
			return primary == other.primary && secondary == other.secondary;
		}

		@Override
		public String toString() {
			return "<<" + primary + ", " + secondary + ">>";
		}
	}
	
	// ---------------- Child counts ---------------- //
	
	protected enum Calculate {
		FRESH, CACHED;
	}

	protected void collectChildren(final Set<Pair> result, Calculate c) {
		for (CostModelNode cmn : children.values()) {
			((OpApplNodeWrapper) cmn).collectAndFreezeEvalCounts(result, c);
		}
	}

	protected void collectAndFreezeEvalCounts(final Set<Pair> result, final Calculate c) {
		if (c == Calculate.FRESH) {
			snapshotEvalCount = this.getEvalCount(c);
			snapshotSecondCount = this.getSecondCount(c);
			childCounts.clear();
			if (snapshotEvalCount > 0 || snapshotSecondCount > 0 || this.isPrimed()) {
				childCounts.add(new Pair(snapshotEvalCount, snapshotSecondCount));
			}
			collectChildren(childCounts, c);
		}
		result.addAll(childCounts);
	}
}