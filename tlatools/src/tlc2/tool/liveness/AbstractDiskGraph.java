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
import tlc2.util.BufferedRandomAccessFile;
import tlc2.util.LongVec;
import tlc2.util.statistics.IBucketStatistics;
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
public abstract class AbstractDiskGraph {
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

	private final String chkptName;
	protected final String metadir;
	protected final BufferedRandomAccessFile nodeRAF;
	protected final BufferedRandomAccessFile nodePtrRAF;
	protected final LongVec initNodes;
	/**
	 * In-memory cache
	 */
	protected GraphNode[] gnodes;

	private final IBucketStatistics outDegreeGraphStats;

	public AbstractDiskGraph(String metadir, int soln, IBucketStatistics graphStats) throws IOException {
		this.metadir = metadir;
		this.outDegreeGraphStats = graphStats;
		this.chkptName = metadir + FileUtil.separator + "dgraph_" + soln;
		String fnameForNodes = metadir + FileUtil.separator + "nodes_" + soln;
		this.nodeRAF = new BufferedRandomAccessFile(fnameForNodes, "rw");
		String fnameForPtrs = metadir + FileUtil.separator + "ptrs_" + soln;
		this.nodePtrRAF = new BufferedRandomAccessFile(fnameForPtrs, "rw");
		this.initNodes = new LongVec(1);
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
		// Make array length a function of the available (heap) memory
		this.gnodes = new GraphNode[65536];
	}

	public final void destroyCache() {
		this.gnodes = null;
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
		putNode(node, ptr);
		// Write node to nodePtrRAF:
		this.nodePtrRAF.writeLong(node.stateFP);
		// TODO DiskGraph without a tableau don't need the tindex. The only reason it
		// is written to disk, is to use the same implementation for trace path
		// reconstruction in printTrace/getPath.
		this.nodePtrRAF.writeInt(node.tindex);
		this.nodePtrRAF.writeLongNat(ptr);
		// Write fields of node to nodeRAF:
		node.write(this.nodeRAF);
		return ptr;
	}
	
	protected abstract void putNode(GraphNode node, long ptr);

	/* Get the graph node at the file location ptr. */
	public final GraphNode getNode(final long stateFP, final int tidx, final long ptr) throws IOException {
		// Get from memory cache if cached:
		//TODO Adapt mask to array length iff array length is a func of available memory
		int idx = (int) (stateFP + tidx) & 0xFFFF;
		GraphNode gnode = this.gnodes[idx];
		if (gnode != null && gnode.stateFP == stateFP && gnode.tindex == tidx) {
			return gnode;
		}
		
		// If the node is not found in the in-memory cache, the ptr has to be
		// positive. BufferedRandomAccessFile#seek will throw an IOException due
		// to "negative seek offset" anyway. Lets catch it early on!
		if (ptr < 0) {
			throw new IllegalArgumentException("Invalid negative file pointer: " + ptr);
		}

		// Have to get the node from disk:
		long curPtr = this.nodeRAF.getFilePointer();
		this.nodeRAF.seek(ptr);

		GraphNode gnode1 = new GraphNode(stateFP, tidx);
		gnode1.read(this.nodeRAF);
		
		this.nodeRAF.seek(curPtr);

		// Add to in-memory cache
		if (gnode == null) {
			this.gnodes[idx] = gnode1;
		}
		return gnode1;
	}

	/* Create the in-memory node-pointer table from the node-pointer file. */
	public final void makeNodePtrTbl() throws IOException {
		long ptr = this.nodePtrRAF.getFilePointer();
		long len = this.nodePtrRAF.length();
		this.makeNodePtrTbl(len);
		this.nodePtrRAF.seek(ptr);
	}

	protected abstract void makeNodePtrTbl(final long ptr) throws IOException;

	/* Return the link assigned to the node. */
	public abstract long getLink(long state, int tidx);

	/**
	 * Assign link to node. If a link has already been assigned to the node,
	 * does nothing by simply returning the existing link. Otherwise, add <node,
	 * link> into the table and return -1.
	 */
	public abstract long putLink(long state, int tidx, long link);

	public abstract void setMaxLink(long state, int tidx);

	/**
	 * Return the shortest path (inclusive and in reverse order) from some
	 * initial state to state. The path is a vector of states <s1, s2, ..., sn>,
	 * where s1 is state, sn is an initial state, and si -> si-1 is a state
	 * transition.
	 */
	public LongVec getPath(final long state, final int tidx) throws IOException {
		throw new RuntimeException("Couldn't re-create liveness trace (path) starting at: " + state + " and tidx: "
				+ tidx);
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
	public abstract String toDotViz();

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

	public abstract void reset() throws IOException;

	// This method is not called anywhere because *out degree* graph statistics are collected
	// during liveness checking with negligible overhead (see DiskGraph#addNode).
	public void calculateOutDegreeDiskGraph(final IBucketStatistics outDegreeGraphStats) throws IOException {
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
	
	public void calculateInDegreeDiskGraph(final IBucketStatistics inDegreeGraphStats) throws IOException {
		//TODO This only supports 2^31 map elements and thus less of what TLC can handle. A
		// longlong FPSet with a user defined mask could be used to store 2^63.
		final Map<NodeRAFRecord, Integer> nodes2count = new HashMap<NodeRAFRecord, Integer>();
		
		// One-pass (start to end) through the nodeRAF file reading all "records".
		// A record is a combination of a state's fingerprint and a tableau id.
		// Together they uniquely identify a vertex in the graph.
		// The nodeRAF is the secondary disk storage file of the disk graph. It
		// contains vertices that are successors of a vertex stored in the nodePtrRAF.
		// The nodePtrRAF is the primary disk storage file with a fingerprint & 
		// tableau id and a pointer to the successor nodes in nodeRAF. While 
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

		private AbstractDiskGraph getOuterType() {
			return AbstractDiskGraph.this;
		}
	}
}
