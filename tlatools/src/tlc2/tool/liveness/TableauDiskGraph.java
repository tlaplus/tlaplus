package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.LongVec;
import tlc2.util.MemIntQueue;
import tlc2.util.statistics.IBucketStatistics;

public class TableauDiskGraph extends AbstractDiskGraph {
	
	private static final long INIT_STATE = MAX_PTR + 1;

	private TableauNodePtrTable nodePtrTbl;
	
	public TableauDiskGraph(String metadir, int soln, IBucketStatistics graphStats) throws IOException {
		super(metadir, soln, graphStats);
		this.nodePtrTbl = new TableauNodePtrTable(255);
	}
	
	public final boolean isDone(long fp) {
		return this.nodePtrTbl.isDone(fp);
	}

	public final int setDone(long fp) {
		return this.nodePtrTbl.setDone(fp);
	}

	public final long getPtr(long fp, int tidx) {
		return this.nodePtrTbl.get(fp, tidx);
	}
	
	public int getElemLength() {
		return this.nodePtrTbl.getElemLength();
	}

	/**
	 * This method records that the node, whose fingerprint is fp, is reachable.
	 * The node itself is not added into the graph.
	 */
	public final void recordNode(long fp, int tidx) {
		this.nodePtrTbl.put(fp, tidx, 0xFFFFFFFE00000000L);
	}

	public final int[] getNodesByLoc(int loc) {
		return this.nodePtrTbl.getNodesByLoc(loc);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#putNode(tlc2.tool.liveness.GraphNode, long)
	 */
	protected void putNode(GraphNode node, long ptr) {
		this.nodePtrTbl.put(node.stateFP, node.tindex, ptr);
	}

	/* Get the graph node. Return null if the node is not in this. */
	public final GraphNode getNode(long fp, int tidx) throws IOException {
		long ptr = this.nodePtrTbl.get(fp, tidx);
		if (ptr < 0) {
			return null;
		}
		return this.getNode(fp, tidx, ptr);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#getLink(long, int)
	 */
	public long getLink(long state, int tidx) {
		return this.nodePtrTbl.get(state, tidx);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#putLink(long, int, long)
	 */
	public long putLink(long state, int tidx, long link) {
		int[] node = this.nodePtrTbl.getNodes(state);
		int cloc = this.nodePtrTbl.getIdx(node, tidx);
		long oldLink = TableauNodePtrTable.getElem(node, cloc);
		if (!isFilePointer(oldLink)) {
			return oldLink;
		}
		TableauNodePtrTable.putElem(node, link, cloc);
		return -1;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#setMaxLink(long, int)
	 */
	public void setMaxLink(long state, int tidx) {
		this.nodePtrTbl.put(state, tidx, MAX_LINK);
	}

	public final void reset() throws IOException {
		this.nodePtrRAF.setLength(0);
		this.nodeRAF.setLength(0);
		this.nodePtrTbl = new TableauNodePtrTable(255);
	 }

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#makeNodePtrTbl(long)
	 */
	protected void makeNodePtrTbl(final long ptr) throws IOException  {
		makeNodePtrTbl(ptr, nodePtrTbl);
	}
	
	protected void makeNodePtrTbl(final long ptr, final TableauNodePtrTable aTable) throws IOException  {
		this.nodePtrRAF.seek(0);
		while (this.nodePtrRAF.getFilePointer() < ptr) {
			long fp = this.nodePtrRAF.readLong();
			int tidx = this.nodePtrRAF.readInt();
			long loc = this.nodePtrRAF.readLongNat();
			aTable.put(fp, tidx, loc);
		}
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public final String toString() {

		// The following code relies on gnodes not being null, thus safeguard
		// against accidental invocations.
		// Essentially one has to wrap the toString call with
		// createCache/destroyCache
		// for gnodes to be initialized.
		if (this.gnodes == null) {
			return "";
		}

		StringBuffer sb = new StringBuffer();
		try {
			long nodePtr = this.nodeRAF.getFilePointer();
			long nodePtrPtr = this.nodePtrRAF.getFilePointer();
			long len = this.nodePtrRAF.length();
			this.nodePtrRAF.seek(0);
			while (this.nodePtrRAF.getFilePointer() < len) {
				long fp = nodePtrRAF.readLong();
				int tidx = nodePtrRAF.readInt();
				long loc = nodePtrRAF.readLongNat();
				sb.append("<" + fp + "," + tidx + "> -> ");
				GraphNode gnode = this.getNode(fp, tidx, loc);
				int sz = gnode.succSize();
				for (int i = 0; i < sz; i++) {
					sb.append("<" + gnode.getStateFP(i) + "," + gnode.getTidx(i) + "> ");
				}
				sb.append("\n");
			}
			this.nodeRAF.seek(nodePtr);
			this.nodePtrRAF.seek(nodePtrPtr);
		} catch (IOException e) {
			MP.printError(EC.SYSTEM_DISKGRAPH_ACCESS, e);

			System.exit(1);
		}
		return sb.toString();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#toDotViz()
	 */
	public final String toDotViz() {

		// The following code relies on gnodes not being null, thus safeguard
		// against accidental invocations.
		// Essentially one has to wrap the toDotViz call with
		// createCache/destroyCache
		// for gnodes to be initialized.
		if (this.gnodes == null) {
			return "";
		}

		StringBuffer sb = new StringBuffer();
		try {
			sb.append("digraph DiskGraph {\n");
			sb.append("nodesep = 0.7\n");
			sb.append("rankdir=LR;\n"); // Left to right rather than top to bottom
			long nodePtr = this.nodeRAF.getFilePointer();
			long nodePtrPtr = this.nodePtrRAF.getFilePointer();
			long len = this.nodePtrRAF.length();
			this.nodePtrRAF.seek(0);
			while (this.nodePtrRAF.getFilePointer() < len) {
				long fp = nodePtrRAF.readLong();
				int tidx = nodePtrRAF.readInt();
				long loc = nodePtrRAF.readLongNat();
				GraphNode gnode = this.getNode(fp, tidx, loc);
				sb.append(gnode.toDotViz(isInitState(gnode)));
			}
			sb.append("}");
			this.nodeRAF.seek(nodePtr);
			this.nodePtrRAF.seek(nodePtrPtr);
		} catch (IOException e) {
			MP.printError(EC.SYSTEM_DISKGRAPH_ACCESS, e);

			System.exit(1);
		}
		return sb.toString();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.AbstractDiskGraph#getPath(long, int)
	 */
	public final LongVec getPath(final long state, final int tidx) throws IOException {
		// If path requested just consists of an init node, return the single
		// init node. This is the trivial case.
		final int numOfInits = this.initNodes.size();
		for (int i = 0; i < numOfInits; i += 2) {
			final long state0 = this.initNodes.elementAt(i);
			if (state0 == state) {
				final LongVec res = new LongVec(1);
				res.addElement(state0);
				return res;
			}
		}
		// ...the path consists of more than just a single init node:

		// Restore the nodePtrTbl. The implementation uses the efficient
		// NodePtrTable because it is doing a breadth-first search and thus
		// potentially traversing many many nodes:
		// Restoring/Resetting the NodePtrTable is crucial as we are going to
		// store elements exclusively used for the reverse path reconstruction.
		// They are incompatible with the way other parts of the code use the
		// NodePtrTable.
		final TableauNodePtrTable reversablePtrTable = new ReverseTraversableTableauNodePtrTable(255);
		this.makeNodePtrTbl(this.nodePtrRAF.length(), reversablePtrTable);

		// Do breadth-first search (BFS guarantees we find the *shortest* path
		// which is most comprehensible):
		final MemIntQueue queue = new MemIntQueue(this.metadir, null);

		// Add all init states to nodePtrTable (some might already be in
		// nodePtrTable) and mark all init states in nodePtrTable as such. Note
		// that a nodes init state property does not solely depend on its
		// fingerprint. It depends on the fingerprint *and* tableau idx.:
		for (int i = 0; i < numOfInits; i += 2) {
			final long state0 = this.initNodes.elementAt(i);
			final int tidx0 = (int) this.initNodes.elementAt(i + 1);
			queue.enqueueLong(state0);
			queue.enqueueInt(tidx0);
			queue.enqueueLong(reversablePtrTable.get(state0, tidx0));
			// Marker the node as an init state in nodePtrTable. This is used
			// below when the reverse path gets reconstructed as a termination
			// condition.
			reversablePtrTable.put(state0, tidx0, MAX_PTR);
		}

		// While queue has elements, but not longer! while(true)... can get stuck 
		while (queue.hasElements()) {
			final long curState = queue.dequeueLong();
			final int curTidx = queue.dequeueInt();
			final long curPtr = queue.dequeueLong();
			final GraphNode curNode = this.getNode(curState, curTidx, curPtr);
			final int succCnt = curNode.succSize();

			for (int i = 0; i < succCnt; i++) {
				final long nextState = curNode.getStateFP(i);
				final int nextTidx = curNode.getTidx(i);
				if (nextState == curState && nextTidx == curTidx) {
					// No point to explore a successor state
					// that is the current state. It is a successor
					// due to a direct cycle in the graph.
					continue;
				}
				if (nextState == state && nextTidx == tidx) {
					// Stop BFS (see MemIntQUEUE above), we found a path to state.
					return reconstructReversePath(reversablePtrTable, curState, curTidx, nextState);
				}

				// Lookup the successor nodes of nextState (curState -> nextState ->
				// successor nodes).
				final int nextLoc = reversablePtrTable.getNodesLoc(nextState);
				final int[] nextNodes = reversablePtrTable.getNodesByLoc(nextLoc);
				final int cloc = reversablePtrTable.getIdx(nextNodes, nextTidx);
				final long nextPtr = TableauNodePtrTable.getElem(nextNodes, cloc);

				// Add nextState to the queue if its successor node are still on disk.
				if (isFilePointer(nextPtr)) {
					// nextState is not visited: enqueue it, mark it
					// visited, and memorize its parent.
					queue.enqueueLong(nextState);
					queue.enqueueInt(nextTidx);
					queue.enqueueLong(nextPtr);
					final int curLoc = reversablePtrTable.getNodesLoc(curState);
					// Add extra information to the back-pointer pointing to the
					// predecessor to not just map to the state, but
					// additionally to the specific tableau idx.
					reversablePtrTable.putElem(nextNodes, INIT_STATE + curLoc, curTidx, cloc);
				}
			}
		}
		return super.getPath(state, tidx);
	}

	private LongVec reconstructReversePath(final TableauNodePtrTable reversablePtrTable, final long startState,
			final int startTidx, final long finalState) {
		// Add the target/final state to the result. Reverse path construction
		// does not start at the final state that the getPath(..) is searching
		// for, but at its immediate predecessor alias startState. 
		final LongVec res = new LongVec(2);
		res.addElement(finalState);
		
		// Traverse the graph backwards from currentState using
		// the NodePtrTable. The NodePtrTable contains the back
		// pointers from a successor to its predecessor.
		long currentState = startState;
		int currentTidx = startTidx;
		int currentLoc = reversablePtrTable.getNodesLoc(currentState);
		int[] nodes = reversablePtrTable.getNodesByLoc(currentLoc);
		while (true) {
			// res never empty due to addElement call with final
			// state.
			if (res.lastElement() == currentState) {
				// The new state is the last state in res, we are about
				// to follow a cycle, thus exit.
				throw new RuntimeException("Self loop in trace path reconstruction");
			}
			res.addElement(currentState);
			long predecessorLocation = -1;
			int predecessorTidx = -1;
			for (int j = 2; j < nodes.length; j += reversablePtrTable.getElemLength()) {
				// a) The node's tableau idx has to match the one we
				// are interested in.
				// b) All nodes have been read from disk during the
				// outer BFS. If the node is still on disk, it can't
				// be part of the path, thus ignore.
				final long candidateLocation = TableauNodePtrTable.getElem(nodes, j);
				final int candidateTidx = TableauNodePtrTable.getTidx(nodes, j);
				if (currentTidx == candidateTidx && !isFilePointer(candidateLocation)) {
					predecessorLocation = candidateLocation;
					predecessorTidx = reversablePtrTable.getElemTidx(nodes, j);
					if (candidateLocation == MAX_PTR) {
						// The predecessor is an init state and thus the best
						// match (on our search for the shortest path) out of
						// all possible predecessors. No need to continue the
						// search...
						break;
					}
					// ...else we continue looping over all predecessors
					// returning the last match (not an init state though).
				}
				// Ignore the else case, because the outer while
				// loop would have read the node from disk if it
				// came across it in the BFS. Since it didn't read
				// during BFS, it won't be part of the path anyway.
			}
			// MAX_PTR indicates that this is an init state. Since
			// getPath is looking for the shortest path from the
			// given state back to *an* initial state, we are done.
			if (predecessorLocation == MAX_PTR) {
				break;
			}
			// Lookup the predecessor in the ptr table. (ploc -
			// offset) is the index of the predecessor in the
			// nodePtrTbl. See offset below at putByLoc(..).
			currentLoc = (int) (predecessorLocation - INIT_STATE);
			nodes = reversablePtrTable.getNodesByLoc(currentLoc);
			currentState = TableauNodePtrTable.getKey(nodes);
			currentTidx = predecessorTidx;
		}
		return res;
	}
	
	private class ReverseTraversableTableauNodePtrTable extends TableauNodePtrTable {

		public ReverseTraversableTableauNodePtrTable(final int size) {
			super(size);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.TableauNodePtrTable#getElemTidx(int[], int)
		 */
		public int getElemTidx(final int[] node, final int loc) {
			return node[loc + 3];
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.TableauNodePtrTable#putElem(int[], long, int, int)
		 */
		public void putElem(final int[] node, final long elem, final int tableauIdx, final int loc) {
			super.putElem(node, elem, tableauIdx, loc);
			node[loc + 3] = tableauIdx;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.TableauNodePtrTable#getElemLength()
		 */
		public int getElemLength() {
			// This implementation stores the predecessor's tableau index
			// additionally to its location in this ptr table.
			return super.getElemLength() + 1;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.TableauNodePtrTable#addElem(long, int, long)
		 */
		protected int[] addElem(final long key, final int tidx, final long elem) {
			final int[] node = super.addElem(key, tidx, elem);
			node[5] = -1; // later updated to store predecessor's tidx
			return node;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.TableauNodePtrTable#addElem(int[], int, long)
		 */
		protected int[] addElem(final int[] node, final int tidx, final long elem) {
			int len = node.length;
			int[] newNode = new int[len + getElemLength()];
			System.arraycopy(node, 0, newNode, 0, len);
			newNode[len] = tidx;
			newNode[len + 1] = (int) (elem >>> 32);
			newNode[len + 2] = (int) (elem & 0xFFFFFFFFL);
			newNode[len + 3] = -1; // later used to store predecessor's tidx
			return newNode;
		}
	}
}
