// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:36 PST by lamport
//      modified on Sat Dec 29 22:15:18 PST 2001 by yuanyu

package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.LongVec;
import tlc2.util.MemIntQueue;
import tlc2.util.statistics.IBucketStatistics;

/**
 * A {@link DiskGraph} is an implementation of {@link AbstractDiskGraph}. It has
 * *not* tableau!
 * 
 * @see TableauDiskGraph for a version with tableau support.
 */
// TODO This implementation still (legacy) writes an int "-1" tableau id for
// each node. This should be removed! TODO markers are indicate the code
// positions that need changing.
public class DiskGraph extends AbstractDiskGraph {

	private NodePtrTable nodePtrTbl;
	
	public DiskGraph(String metadir, int soln, IBucketStatistics graphStats) throws IOException {
		super(metadir, soln, graphStats);
		nodePtrTbl = new NodePtrTable(255);
	}

	/* Get the graph node. Return null if the node is not in this. */
	public final GraphNode getNode(long stateFP) throws IOException {
		long ptr = this.nodePtrTbl.get(stateFP);
		if (ptr < 0) {
			return null;
		}
		return this.getNode(stateFP, -1, ptr);
	}

	public final long getPtr(long fp) {
		return this.nodePtrTbl.get(fp);
	}


	public void reset() throws IOException {
		this.nodePtrRAF.setLength(0);
		this.nodeRAF.setLength(0);
		this.nodePtrTbl = new NodePtrTable(255);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#putNode(tlc2.tool.liveness.GraphNode, long)
	 */
	protected void putNode(GraphNode node, long ptr) {
		this.nodePtrTbl.put(node.stateFP, ptr);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#getLink(long, int)
	 */
	public long getLink(long state, int tidx) {
		return this.nodePtrTbl.get(state);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#putLink(long, int, long)
	 */
	public long putLink(long state, int tidx, long link) {
		int loc = this.nodePtrTbl.getLoc(state);
		long oldLink = this.nodePtrTbl.getByLoc(loc);
		if (!isFilePointer(oldLink)) {
			return oldLink;
		}
		this.nodePtrTbl.putByLoc(state, link, loc);
		return -1;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#setMaxLink(long, int)
	 */
	public void setMaxLink(long state, int tidx) {
		this.nodePtrTbl.put(state, MAX_LINK);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraph#makeNodePtrTbl(long)
	 */
	protected void makeNodePtrTbl(long ptr) throws IOException {
		this.nodePtrRAF.seek(0);
		while (this.nodePtrRAF.getFilePointer() < ptr) {
			long fp = this.nodePtrRAF.readLong();
			// SZ Jul 13, 2009: removed to kill the warning
			// SZ Feb 20, 2009: variable never read locally
			// int tidx =
			this.nodePtrRAF.readInt();
			long loc = this.nodePtrRAF.readLongNat();
			this.nodePtrTbl.put(fp, loc);
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
				sb.append(fp + " -> ");
				GraphNode gnode = this.getNode(fp, tidx, loc);
				int sz = gnode.succSize();
				for (int i = 0; i < sz; i++) {
					sb.append(gnode.getStateFP(i) + " ");
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
			sb.append("rankdir=LR;"); // Left to right rather than top to bottom
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
	public final LongVec getPath(final long state, final int tidxIgnored) throws IOException {
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
			long ptr = this.nodePtrTbl.get(state0);
			// Skip initial states without successors:
			// An initial state with a -1 (disk) pointer means that is has *no*
			// successors. Thus, it can safely be omitted from the path search
			// below. If the init state is the very state searched for, the
			// previous for loop will have caught it already.
			// Adding an init with negative pointer to the queue manifests in
			// an exception in the while loop below. This is because the
			// DiskGraph won't be able to return a GraphNode instance.
			if (ptr != -1) {
				queue.enqueueLong(state0);
				queue.enqueueLong(ptr);
				this.nodePtrTbl.put(state0, MAX_PTR);
			}
		}

		while (queue.hasElements()) {
			long curState = queue.dequeueLong();
			final long curPtr = queue.dequeueLong();
			final GraphNode curNode = this.getNode(curState, -1, curPtr);
			final int succCnt = curNode.succSize();

			for (int i = 0; i < succCnt; i++) {
				final long nextState = curNode.getStateFP(i);
				if (nextState == state) {
					// found a path to state: construct the path and return.
					final LongVec res = new LongVec(2);
					res.addElement(nextState);
					int curLoc = this.nodePtrTbl.getLoc(curState);
					while (true) {
						res.addElement(curState);
						final long ploc = this.nodePtrTbl.getByLoc(curLoc);
						// MAX_PTR indicates that this is an init state. Since
						// getPath is looking for the shortest path from the
						// given state back to *an* initial state, we are done.
						if (ploc == MAX_PTR) {
							break;
						}
						// Lookup the predecessor in the ptr table. (ploc -
						// offset) is the index of the predecessor in the
						// nodePtrTbl. See offset below at putByLoc(..).
						curLoc = (int) (ploc - offset);
						curState = this.nodePtrTbl.getKeyByLoc(curLoc);
					}
					return res;
				}
				final int nextLoc = this.nodePtrTbl.getLoc(nextState);
				final long nextPtr = this.nodePtrTbl.getByLoc(nextLoc);
				if (isFilePointer(nextPtr)) {
					// nextState is not visited:
					queue.enqueueLong(nextState);
					queue.enqueueLong(nextPtr);
					final int curLoc = this.nodePtrTbl.getLoc(curState);
					this.nodePtrTbl.putByLoc(nextState, offset + curLoc, nextLoc);
				}
			}
		}
		return super.getPath(state, tidxIgnored);
	}
}
