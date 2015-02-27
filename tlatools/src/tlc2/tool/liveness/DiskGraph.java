// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:36 PST by lamport
//      modified on Sat Dec 29 22:15:18 PST 2001 by yuanyu

package tlc2.tool.liveness;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.BitVector;
import tlc2.util.BufferedRandomAccessFile;
import tlc2.util.LongVec;
import tlc2.util.MemIntQueue;
import tlc2.util.statistics.BucketStatistics;
import util.FileUtil;

/*
 * Notes Markus 02/13/2015
 * 
 * - A {@link DiskGraph} has a 1:1 relationship with {@link OrderOfSolution}
 * 
 * - Logically stores the triple of state, tableaux, link (transitions)
 * -- Technically does *not* store States, but only a state's fingerprints
 * --- Stores a fingerprint split into 2 ints (low & high part of a fingerprint)
 * -- Stores the index of the tableaux, not the tableaux itself
 * --- The TableauGraphNode (TBGraphNode) instance can be obtained by reading
 *     the DiskGraph triple into a GraphNode instance and calling 
 *     GraphNode#getTNode(TBGraph). One obviously has to have access to the TBGraph
 * -- Link(s) are kept in GraphNode#nnodes
 *
 * - {@link DiskGraph#toString()} does not print init nodes. They never get 
 *   written to the {@link BufferedRandomAccessFile}s {@link DiskGraph#nodePtrRAF}
 *   & {@link DiskGraph#nodeRAF} 
 * - {@link DiskGraph#toString()} only prints the part of the DiskGraph that is on
 *   disk. It ignores the in-memory part. This means toString produces *no* output
 *   for as long as the graph has *not* been flushed to disk
 * 
 * - On disk, the {@link BufferedRandomAccessFile}s are suffixed by the ID of the
 *   {@link DiskGraph} (we can have >1 when there are more {@link OrderOfSolution})
 */
public class DiskGraph {
	/**
	 * DiskGraph stores a graph on disk. We use two disk files to store the
	 * graph. For each node in the graph, the first file stores the successors
	 * and information we precompute for the node, and the second file stores
	 * the fingerprint of the node and a pointer to the location of the node in
	 * the first file.
	 *
	 * The field nodePtrTbl is initially set to contain all (node, ptr) pairs in
	 * the file fileForPtrs. It is then used to store the link in the SCC
	 * computation. We assume that the length of the file fileForPtrs is less
	 * than MAX_PTR, and use numbers between MAX_PTR and MAX_LINK for links. So,
	 * it is a file pointer iff ptr < MAX_PTR.
	 *
	 * We cache portions of the graph in memory.
	 */

	/* The maximum length of the file fileForNodes. */
	public static final long MAX_PTR = 0x4000000000000000L;

	/* Links are from MAX_PTR and MAX_LINK. */
	public static final long MAX_LINK = 0x7FFFFFFFFFFFFFFFL;

	public static boolean isFilePointer(long loc) {
		return loc < MAX_PTR;
	}

	private String metadir;
	private String chkptName;
	private BufferedRandomAccessFile nodeRAF;
	private BufferedRandomAccessFile nodePtrRAF;
	private NodePtrTable nodePtrTbl;
	private LongVec initNodes;
	private boolean hasTableau;
	private GraphNode[] gnodes;

	private final BucketStatistics outDegreeGraphStats;

	public DiskGraph(String metadir, int soln, boolean hasTableau, final BucketStatistics graphStats) throws IOException {
		this.metadir = metadir;
		this.outDegreeGraphStats = graphStats;
		this.chkptName = metadir + FileUtil.separator + "dgraph_" + soln;
		String fnameForNodes = metadir + FileUtil.separator + "nodes_" + soln;
		this.nodeRAF = new BufferedRandomAccessFile(fnameForNodes, "rw");
		String fnameForPtrs = metadir + FileUtil.separator + "ptrs_" + soln;
		this.nodePtrRAF = new BufferedRandomAccessFile(fnameForPtrs, "rw");
		this.nodePtrTbl = new NodePtrTable(255, hasTableau);
		this.initNodes = new LongVec(1);
		this.hasTableau = hasTableau;
		this.gnodes = null;
	}

	public final void addInitNode(long node, int tidx) {
		this.initNodes.addElement(node);
		this.initNodes.addElement(tidx);
	}

	public final LongVec getInitNodes() {
		return this.initNodes;
	}

	public final void createCache() {
		this.gnodes = new GraphNode[65536];
	}

	public final void destroyCache() {
		this.gnodes = null;
	}

	public final boolean isDone(long fp) {
		return this.nodePtrTbl.isDone(fp);
	}

	public final int setDone(long fp) {
		return this.nodePtrTbl.setDone(fp);
	}

	/**
	 * This method records that the node, whose fingerprint is fp, is reachable.
	 * The node itself is not added into the graph.
	 */
	public final void recordNode(long fp, int tidx) {
		this.nodePtrTbl.put(fp, tidx, 0xFFFFFFFE00000000L);
	}

	/* Close the disk files. */
	public final void close() throws IOException {
		this.nodeRAF.close();
		this.nodePtrRAF.close();
	}

	/**
	 * Add the given graph node into this graph. Return the location of this
	 * node in the node file.
	 */
	public final long addNode(GraphNode node) throws IOException {
		outDegreeGraphStats.addSample(node.succSize());
		
		long ptr = this.nodeRAF.getFilePointer();

		// Write node to nodePtrTbl:
		if (this.hasTableau) {
			this.nodePtrTbl.put(node.stateFP, node.tindex, ptr);
		} else {
			this.nodePtrTbl.put(node.stateFP, ptr);
		}
		// Write node to nodePtrRAF:
		this.nodePtrRAF.writeLong(node.stateFP);
		this.nodePtrRAF.writeInt(node.tindex);
		this.nodePtrRAF.writeLongNat(ptr);
		// Write fields of node to nodeRAF:
		int cnt = node.nnodes.length;
		this.nodeRAF.writeNat(cnt);
		for (int i = 0; i < cnt; i++) {
			this.nodeRAF.writeInt(node.nnodes[i]);
		}
		node.checks.write(this.nodeRAF);
		return ptr;
	}

	/* Get the graph node at the file location ptr. */
	public final GraphNode getNode(long stateFP, int tidx, long ptr) throws IOException {
		// Get from memory cache if cached:
		int idx = (int) (stateFP + tidx) & 0xFFFF;
		GraphNode gnode = this.gnodes[idx];
		if (gnode != null && gnode.stateFP == stateFP && gnode.tindex == tidx) {
			return gnode;
		}

		// Have to get the node from disk:
		long curPtr = this.nodeRAF.getFilePointer();
		this.nodeRAF.seek(ptr);
		int cnt = this.nodeRAF.readNat();
		int[] nnodes = new int[cnt];
		for (int i = 0; i < cnt; i++) {
			nnodes[i] = this.nodeRAF.readInt();
		}
		BitVector checks = new BitVector();
		checks.read(this.nodeRAF);
		this.nodeRAF.seek(curPtr);

		GraphNode gnode1 = new GraphNode(stateFP, tidx, nnodes, checks);
		// Add to in-memory cache
		if (gnode == null) {
			this.gnodes[idx] = gnode1;
		}
		return gnode1;
	}

	/* Get the graph node. Return null if the node is not in this. */
	public final GraphNode getNode(long stateFP) throws IOException {
		long ptr = this.nodePtrTbl.get(stateFP);
		if (ptr < 0) {
			return null;
		}
		return this.getNode(stateFP, -1, ptr);
	}

	/* Get the graph node. Return null if the node is not in this. */
	public final GraphNode getNode(long fp, int tidx) throws IOException {
		long ptr = this.nodePtrTbl.get(fp, tidx);
		if (ptr < 0) {
			return null;
		}
		return this.getNode(fp, tidx, ptr);
	}

	public final long getPtr(long fp) {
		return this.nodePtrTbl.get(fp);
	}

	public final long getPtr(long fp, int tidx) {
		return this.nodePtrTbl.get(fp, tidx);
	}

	public final int[] getNodes(long stateFP) {
		return this.nodePtrTbl.getNodes(stateFP);
	}

	public final int[] getNodesByLoc(int loc) {
		return this.nodePtrTbl.getNodesByLoc(loc);
	}

	/* Create the in-memory node-pointer table from the node-pointer file. */
	public final void makeNodePtrTbl() throws IOException {
		long ptr = this.nodePtrRAF.getFilePointer();
		long len = this.nodePtrRAF.length();
		this.makeNodePtrTbl(len);
		this.nodePtrRAF.seek(ptr);
	}

	public final void makeNodePtrTbl(long ptr) throws IOException {
		this.nodePtrRAF.seek(0);
		if (this.hasTableau) {
			while (this.nodePtrRAF.getFilePointer() < ptr) {
				long fp = this.nodePtrRAF.readLong();
				int tidx = this.nodePtrRAF.readInt();
				long loc = this.nodePtrRAF.readLongNat();
				this.nodePtrTbl.put(fp, tidx, loc);
			}
		} else {
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
	}

	public final boolean isGood() {
		return this.nodePtrTbl.isGood();
	}

	/* Return the link assigned to the node. */
	public final long getLink(long state, int tidx) {
		if (this.hasTableau) {
			return this.nodePtrTbl.get(state, tidx);
		} else {
			return this.nodePtrTbl.get(state);
		}
	}

	/**
	 * Assign link to node. If a link has already been assigned to the node,
	 * does nothing by simply returning the existing link. Otherwise, add <node,
	 * link> into the table and return -1.
	 */
	public final long putLink(long state, int tidx, long link) {
		if (this.hasTableau) {
			int[] node = this.nodePtrTbl.getNodes(state);
			int cloc = NodePtrTable.getIdx(node, tidx);
			long oldLink = NodePtrTable.getElem(node, cloc);
			if (!isFilePointer(oldLink)) {
				return oldLink;
			}
			NodePtrTable.putElem(node, link, cloc);
		} else {
			int loc = this.nodePtrTbl.getLoc(state);
			long oldLink = this.nodePtrTbl.getByLoc(loc);
			if (!isFilePointer(oldLink)) {
				return oldLink;
			}
			this.nodePtrTbl.putByLoc(state, link, loc);
		}
		return -1;
	}

	public final void setMaxLink(long state, int tidx) {
		if (this.hasTableau) {
			this.nodePtrTbl.put(state, tidx, MAX_LINK);
		} else {
			this.nodePtrTbl.put(state, MAX_LINK);
		}
	}

	/**
	 * Return the shortest path (inclusive and in reverse order) from some
	 * initial state to state. The path is a vector of states <s1, s2, ..., sn>,
	 * where s1 is state, sn is an initial state, and si -> si-1 is a state
	 * transition.
	 */
	public final LongVec getPath(long state) throws IOException {
		int numOfInits = this.initNodes.size();
		for (int i = 0; i < numOfInits; i += 2) {
			long state0 = this.initNodes.elementAt(i);
			// SZ Jul 13, 2009: removed to kill the warning
			// SZ Feb 20, 2009: variable never read locally
			// int tidx0 = (int)
			this.initNodes.elementAt(i + 1);
			if (state0 == state) {
				LongVec res = new LongVec(1);
				res.addElement(state0);
				return res;
			}
		}

		// Restore the nodePtrTbl:
		this.makeNodePtrTbl();

		// Do breath-first search:
		long offset = MAX_PTR + 1;
		MemIntQueue queue = new MemIntQueue(this.metadir, null);

		if (this.hasTableau) {
			// Initialize queue with initial states:
			for (int i = 0; i < numOfInits; i += 2) {
				long state0 = this.initNodes.elementAt(i);
				int tidx0 = (int) this.initNodes.elementAt(i + 1);
				queue.enqueueLong(state0);
				queue.enqueueInt(tidx0);
				queue.enqueueLong(this.nodePtrTbl.get(state0, tidx0));
				this.nodePtrTbl.put(state0, tidx0, MAX_PTR);
			}

			while (true) {
				long curState = queue.dequeueLong();
				int curTidx = queue.dequeueInt();
				long curPtr = queue.dequeueLong();
				GraphNode curNode = this.getNode(curState, curTidx, curPtr);
				int succCnt = curNode.succSize();

				for (int i = 0; i < succCnt; i++) {
					long nextState = curNode.getStateFP(i);
					if (nextState == curState) {
						// No point to explore a successor state
						// that is the current state. It is a successor
						// due to a direct cycle in the graph.
						continue;
					}
					int nextTidx = curNode.getTidx(i);
					if (nextState == state) {
						// found a path to state:
						LongVec res = new LongVec(2);
						res.addElement(nextState);
						int curLoc = this.nodePtrTbl.getNodesLoc(curState);
						int[] nodes = this.nodePtrTbl.getNodesByLoc(curLoc);
						while (true) {
							res.addElement(curState);
							long ploc = -1;
							for (int j = 2; j < nodes.length; j += 3) {
								ploc = NodePtrTable.getElem(nodes, j);
								if (!isFilePointer(ploc)) {
									break;
								}
							}
							if (ploc == MAX_PTR) {
								break;
							}
							curLoc = (int) (ploc - offset);
							nodes = this.nodePtrTbl.getNodesByLoc(curLoc);
							curState = NodePtrTable.getKey(nodes);
						}
						return res;
					}

					int nextLoc = this.nodePtrTbl.getNodesLoc(nextState);
					int[] nextNodes = this.nodePtrTbl.getNodesByLoc(nextLoc);
					int cloc = NodePtrTable.getIdx(nextNodes, nextTidx);
					long nextPtr = NodePtrTable.getElem(nextNodes, cloc);

					if (isFilePointer(nextPtr)) {
						// nextState is not visited: enqueue it, mark it
						// visited, and
						// memorize its parent.
						queue.enqueueLong(nextState);
						queue.enqueueInt(nextTidx);
						queue.enqueueLong(nextPtr);
						int curLoc = this.nodePtrTbl.getNodesLoc(curState);
						NodePtrTable.putElem(nextNodes, offset + curLoc, cloc);
					}
				}
			}
		} else {
			// Initialize queue with initial states:
			for (int i = 0; i < numOfInits; i += 2) {
				long state0 = this.initNodes.elementAt(i);
				queue.enqueueLong(state0);
				queue.enqueueLong(this.nodePtrTbl.get(state0));
				this.nodePtrTbl.put(state0, MAX_PTR);
			}

			while (true) {
				long curState = queue.dequeueLong();
				long curPtr = queue.dequeueLong();
				GraphNode curNode = this.getNode(curState, -1, curPtr);
				int succCnt = curNode.succSize();

				for (int i = 0; i < succCnt; i++) {
					long nextState = curNode.getStateFP(i);
					if (nextState == state) {
						// found a path to state: construct the path and return.
						LongVec res = new LongVec(2);
						res.addElement(nextState);
						int curLoc = this.nodePtrTbl.getLoc(curState);
						while (true) {
							res.addElement(curState);
							long ploc = this.nodePtrTbl.getByLoc(curLoc);
							if (ploc == MAX_PTR) {
								break;
							}
							curLoc = (int) (ploc - offset);
							curState = this.nodePtrTbl.getKeyByLoc(curLoc);
						}
						return res;
					}
					int nextLoc = this.nodePtrTbl.getLoc(nextState);
					long nextPtr = this.nodePtrTbl.getByLoc(nextLoc);
					if (isFilePointer(nextPtr)) {
						// nextState is not visited:
						queue.enqueueLong(nextState);
						queue.enqueueLong(nextPtr);
						int curLoc = this.nodePtrTbl.getLoc(curState);
						this.nodePtrTbl.putByLoc(nextState, offset + curLoc, nextLoc);
					}
				}
			}
		}
	}

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
			if (this.hasTableau) {
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
			} else {
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
			}
			this.nodeRAF.seek(nodePtr);
			this.nodePtrRAF.seek(nodePtrPtr);
		} catch (IOException e) {
			MP.printError(EC.SYSTEM_DISKGRAPH_ACCESS, e);

			System.exit(1);
		}
		return sb.toString();
	}

	/**
	 * Only useful for debugging.
	 * 
	 * No-OP when not wrapped inside {@link DiskGraph#createCache()} and
	 * {@link DiskGraph#destroyCache()}
	 * 
	 * Copy&Paste output "digraph DiskGraph {...} to a file called graphviz.txt
	 * and call something similar to: 'dot -T svg graphviz.txt -o
	 * "Graphviz.svg"'. It obviously needs Graphviz (http://www.graphviz.org).
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
			if (this.hasTableau) {
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
			} else {
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

	/* Checkpoint. */
	public synchronized final void beginChkpt() throws IOException {
		this.nodeRAF.flush();
		this.nodePtrRAF.flush();
		FileOutputStream fos = new FileOutputStream(this.chkptName + ".chkpt.tmp");
		DataOutputStream dos = new DataOutputStream(fos);
		dos.writeLong(this.nodeRAF.getFilePointer());
		dos.writeLong(this.nodePtrRAF.getFilePointer());
		dos.close();
		fos.close();
	}

	public final void commitChkpt() throws IOException {
		File oldChkpt = new File(this.chkptName + ".chkpt");
		File newChkpt = new File(this.chkptName + ".chkpt.tmp");
		if ((oldChkpt.exists() && !oldChkpt.delete()) || !newChkpt.renameTo(oldChkpt)) {
			throw new IOException("DiskGraph.commitChkpt: cannot delete " + oldChkpt);
		}
	}

	public final void recover() throws IOException {
		FileInputStream fis = new FileInputStream(chkptName + ".chkpt");
		DataInputStream dis = new DataInputStream(fis);
		long nodeRAFPos = dis.readLong();
		long nodePtrRAFPos = dis.readLong();
		dis.close();
		fis.close();

		this.makeNodePtrTbl(nodePtrRAFPos);
		this.nodeRAF.seek(nodeRAFPos);
		this.nodePtrRAF.seek(nodePtrRAFPos);
	}

	// This method is not called anywhere because *out degree* graph statistics are collected
	// during liveness checking with negligible overhead (see DiskGraph#addNode).
	public void calculateOutDegreeDiskGraph(final BucketStatistics outDegreeGraphStats) throws IOException {
		try {
			this.nodePtrRAF.flush();
			this.nodeRAF.flush();
			this.nodePtrRAF.seek(0); // rewind to start
			long len = this.nodePtrRAF.length();
			while (this.nodePtrRAF.getFilePointer() < len) {
				// skip fingerprint a tableaux id
				nodePtrRAF.seek(nodePtrRAF.getFilePointer() + 8 + 4);

				final long ptr = nodePtrRAF.readLongNat();
				nodeRAF.seek(ptr);
				int outArcCount = nodeRAF.readNat() / 3;
				outDegreeGraphStats.addSample(outArcCount);
			}
		} catch (IOException e) {
			MP.printError(EC.SYSTEM_DISKGRAPH_ACCESS, e);
			System.exit(1);
		}
	}
	
	public void calculateInDegreeDiskGraph(final BucketStatistics inDegreeGraphStats) throws IOException {
		//TODO This only supports 2^31 map elements and thus less of what TLC can handle. A
		// longlong FPSet with a user defined mask could be used to store 2^63.
		final Map<NodeRAFRecord, Integer> nodes2count = new HashMap<NodeRAFRecord, Integer>();
		
		// One-pass (start to end) through the nodeRAF file reading all "records".
		// A record is a combination of a state's fingerprint and a tableaux id.
		// Together they uniquely identify a vertex in the graph.
		// The nodeRAF is the secondary disk storage file of the disk graph. It
		// contains vertices that are successors of a vertex stored in the nodePtrRAF.
		// The nodePtrRAF is the primary disk storage file with a fingerprint & 
		// tableaux id and a pointer to the successor nodes in nodeRAF. While 
		// a node appears only once in the nodePtrRAF, the same node is potentially
		// listed in nodeRAF multiple times.
		try {
			this.nodeRAF.flush();
			this.nodeRAF.seek(0); // rewind to start
			long len = this.nodeRAF.length();
			while (this.nodeRAF.getFilePointer() < len) {
				// Get the next cnt nodes from disk:
				int cnt = nodeRAF.readNat() / 3;
				// for each node increment the in arc counter
				for (int i = 0; i < cnt; i++) {
					NodeRAFRecord record = new NodeRAFRecord();
					record.read(this.nodeRAF);
					Integer inArcCounter = nodes2count.get(record);
					if (inArcCounter == null) {
						inArcCounter = new Integer(0);
					}
					nodes2count.put(record, inArcCounter + 1);
				}
				// Skip checks
				// (we don't care for the checks) 
				int checksLen = nodeRAF.readNat();
				nodeRAF.seek(nodeRAF.getFilePointer() + (checksLen * 8)); // 8 bytes is long
			}
		} catch (IOException e) {
			MP.printError(EC.SYSTEM_DISKGRAPH_ACCESS, e);
			System.exit(1);
		}
		
		final Collection<Integer> values = nodes2count.values();
		for (Integer integer : values) {
			inDegreeGraphStats.addSample(integer);
		}
	}
	
	/**
	 * A {@link NodeRAFRecord} is the technical representation of each
	 * record in the NodeRAF file
	 */
	private class NodeRAFRecord {

		private long fp;
		private int tidx;

		public void read(BufferedRandomAccessFile nodeRAF) throws IOException {
			long high = nodeRAF.readInt();
			long low = nodeRAF.readInt();
			fp = (high << 32) | (low & 0xFFFFFFFFL);
			
			tidx = nodeRAF.readInt();
		}

		@Override
		public String toString() {
			return "NodeRAFRecord [fp=" + fp + ", tidx=" + tidx + "]";
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + (int) (fp ^ (fp >>> 32));
			result = prime * result + tidx;
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			NodeRAFRecord other = (NodeRAFRecord) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (fp != other.fp)
				return false;
			if (tidx != other.tidx)
				return false;
			return true;
		}

		private DiskGraph getOuterType() {
			return DiskGraph.this;
		}
	}
}
