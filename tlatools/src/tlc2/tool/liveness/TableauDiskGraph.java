package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.LongVec;
import tlc2.util.MemIntQueue;
import tlc2.util.statistics.BucketStatistics;

public class TableauDiskGraph extends AbstractDiskGraph {

	private final TableauNodePtrTable nodePtrTbl;

	public TableauDiskGraph(String metadir, int soln, BucketStatistics graphStats) throws IOException {
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
		int cloc = TableauNodePtrTable.getIdx(node, tidx);
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

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#makeNodePtrTbl(long)
	 */
	protected void makeNodePtrTbl(long ptr) throws IOException  {
		this.nodePtrRAF.seek(0);
		while (this.nodePtrRAF.getFilePointer() < ptr) {
			long fp = this.nodePtrRAF.readLong();
			int tidx = this.nodePtrRAF.readInt();
			long loc = this.nodePtrRAF.readLongNat();
			this.nodePtrTbl.put(fp, tidx, loc);
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
			long nodePtr = this.nodeRAF.getFilePointer();
			long nodePtrPtr = this.nodePtrRAF.getFilePointer();
			long len = this.nodePtrRAF.length();
			this.nodePtrRAF.seek(0);
			while (this.nodePtrRAF.getFilePointer() < len) {
				long fp = nodePtrRAF.readLong();
				int tidx = nodePtrRAF.readInt();
				long loc = nodePtrRAF.readLongNat();
				GraphNode gnode = this.getNode(fp, tidx, loc);
				int sz = gnode.succSize();
				for (int i = 0; i < sz; i++) {
					sb.append(gnode.toDotViz());
				}
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
	 * @see tlc2.tool.liveness.DiskGraph#getPath(long, int)
	 */
	public final LongVec getPath(final long state) throws IOException {
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

		// Restore the nodePtrTbl:
		this.makeNodePtrTbl();

		// Do breath-first search:
		final long offset = MAX_PTR + 1;
		final MemIntQueue queue = new MemIntQueue(this.metadir, null);

		// Initialize queue with initial states:
		for (int i = 0; i < numOfInits; i += 2) {
			final long state0 = this.initNodes.elementAt(i);
			final int tidx0 = (int) this.initNodes.elementAt(i + 1);
			queue.enqueueLong(state0);
			queue.enqueueInt(tidx0);
			queue.enqueueLong(this.nodePtrTbl.get(state0, tidx0));
			this.nodePtrTbl.put(state0, tidx0, MAX_PTR);
		}

		// While queue has elements, but not longer! while(true)... can get stuck 
		while (queue.hasElements()) {
			long curState = queue.dequeueLong();
			final int curTidx = queue.dequeueInt();
			final long curPtr = queue.dequeueLong();
			final GraphNode curNode = this.getNode(curState, curTidx, curPtr);
			final int succCnt = curNode.succSize();

			for (int i = 0; i < succCnt; i++) {
				final long nextState = curNode.getStateFP(i);
				if (nextState == curState) {
					// No point to explore a successor state
					// that is the current state. It is a successor
					// due to a direct cycle in the graph.
					continue;
				}
				final int nextTidx = curNode.getTidx(i);
				if (nextState == state) {
					// found a path to state:
					final LongVec res = new LongVec(2);
					res.addElement(nextState);
					int curLoc = this.nodePtrTbl.getNodesLoc(curState);
					int[] nodes = this.nodePtrTbl.getNodesByLoc(curLoc);
					while (true) {
						res.addElement(curState);
						long ploc = -1;
						for (int j = 2; j < nodes.length; j += 3) {
							ploc = TableauNodePtrTable.getElem(nodes, j);
							if (!isFilePointer(ploc)) {
								break;
							}
						}
						if (ploc == MAX_PTR) {
							break;
						}
						curLoc = (int) (ploc - offset);
						nodes = this.nodePtrTbl.getNodesByLoc(curLoc);
						curState = TableauNodePtrTable.getKey(nodes);
					}
					return res;
				}

				final int nextLoc = this.nodePtrTbl.getNodesLoc(nextState);
				final int[] nextNodes = this.nodePtrTbl.getNodesByLoc(nextLoc);
				final int cloc = TableauNodePtrTable.getIdx(nextNodes, nextTidx);
				final long nextPtr = TableauNodePtrTable.getElem(nextNodes, cloc);

				if (isFilePointer(nextPtr)) {
					// nextState is not visited: enqueue it, mark it
					// visited, and memorize its parent.
					queue.enqueueLong(nextState);
					queue.enqueueInt(nextTidx);
					queue.enqueueLong(nextPtr);
					final int curLoc = this.nodePtrTbl.getNodesLoc(curState);
					TableauNodePtrTable.putElem(nextNodes, offset + curLoc, cloc);
				}
			}
		}
		throw new RuntimeException("Couldn't re-create liveness trace (path) starting at: " + state);
	}
}
