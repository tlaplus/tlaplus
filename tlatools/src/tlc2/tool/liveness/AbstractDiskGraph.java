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
		// TODO Does not check >= 0 and thus accepts TableauDiskGraph.UNDONE as
		// ptr.
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

	private long sizeAtCheck = 1; // initialize with 1 to avoid div by zero

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

	/**
	 * Creates a fixed size in-memory cache of {@link GraphNode}'s. A disk
	 * lookup is avoid in {@link AbstractDiskGraph#getNode(long, int, long)} on
	 * each cache hit. The cache is destroyed by
	 * {@link AbstractDiskGraph#destroyCache()}.
	 */
	public final void createCache() {
		// Make array length a function of the available (heap) memory. Could
		// approximate the required memory by taking the size of the on-disk
		// files into account, but think of hash collisions!
		this.gnodes = new GraphNode[65536];
	}

	/**
	 * Destroys the fixed size in-memory cache created by
	 * {@link AbstractDiskGraph#createCache()}. This should be done if liveness
	 * checking wants to destroy in-memory {@link GraphNode} nodes to start a
	 * new liveness check on them (e.g. to replace SCC link numbers with the
	 * original disk ptr location).
	 */
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
	 * <p>
	 * Technically adding the same (fingerprint and tableau idx) node *again*
	 * creates a second node in the graph, overwrites the record in the
	 * {@link NodePtrTable}, and writes a second time to the
	 * {@link BufferedRandomAccessFile}s. The reason why it simply writes a new
	 * entry regardless of the node's existence is for performance reasons and
	 * because in regular model checking (not simulation) the set of successors
	 * is identical no matter how often the node is re-written. A file lookup
	 * and a potentially expensive file update (re-align all records due to the
	 * new nnodes count) is thus avoided. The number of distinguishable
	 * {@link GraphNode}s in the graph is therefore stored in the internal
	 * {@link NodePtrTable}. The {@link BufferedRandomAccessFile} length does
	 * not allow to draw a conclusion about the graph's node count.
	 * 
	 * @see commented tlc2.tool.liveness.DiskGraphTest#
	 *      testAddSameGraphN	odeTwiceCorrectSuccessors
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
	
	public abstract GraphNode getNode(long fingerprint, int tableauIdx) throws IOException;
	
	/**
	 * @return true iff the given GraphNode belongs to the set of initial
	 *         states.
	 */
	protected boolean isInitState(final GraphNode gnode) {
		final int numOfInits = initNodes.size();
		for (int j = 0; j < numOfInits; j += 2) {
			final long state = initNodes.elementAt(j);
			final int tidx = (int) initNodes.elementAt(j + 1);
			if (gnode.stateFP == state && gnode.tindex == tidx) {
				return true;
			}
		}
		return false;
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

		GraphNode gnode1 = getNodeFromDisk(stateFP, tidx, ptr);
		// Add to in-memory cache
		if (gnode == null) {
			this.gnodes[idx] = gnode1;
		}
		return gnode1;
	}
	
	protected final GraphNode getNodeFromDisk(final long stateFP, final int tidx, final long ptr) throws IOException {
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
		return gnode1;
	}

	public abstract long getPtr(long l, int tidx);

	/* Create the in-memory node-pointer table from the node-pointer file. */
	public final void makeNodePtrTbl() throws IOException {
		long ptr = this.nodePtrRAF.getFilePointer();
		long len = this.nodePtrRAF.length();
		this.makeNodePtrTbl(len);
		this.nodePtrRAF.seek(ptr);
	}

	/**
	 * This methods reads the node PTR file from disk (the ptr file is the
	 * smaller file ptrs_N of the pair ptrs_N and nodes_N).
	 * <p>
	 * The ptr file contains tuples <<fingerprint, tableau idx, ptr location>>
	 * for all fingerprints times all tableau indices (the corresponding nodes
	 * file contains the outgoing arcs of the node described in the ptr file).
	 * <p>
	 * The reason why the nodePtrTable has to be re-made by calling this method
	 * prior to running the SCC search, is because the ptr location is
	 * eventually overwritten with the nodes link number used by SCC search.
	 * <p>
	 * makeNodePtrTbl maintains/does not overwrite the isDone state of the node,
	 * which - iff true - causes SCC search to skip/ignore the node.
	 * 
	 * @param ptr
	 *            The length of the ptr file up to which this method reads.
	 * @throws IOException
	 *             Reading the file failed
	 */
	protected abstract void makeNodePtrTbl(final long ptr) throws IOException;

	/* Link information for SCC search */
	
	/**
	 * Return the link assigned to the node via putLink() or -1 if the node has
	 * no link assigned yet. Unless -1, the link is in interval [
	 * {@link AbstractDiskGraph#MAX_PTR}, {@link AbstractDiskGraph#MAX_LINK}]
	 * 
	 * @param state
	 *            The state's fingerprint
	 * @param tidx
	 *            The corresponding tableau index
	 */
	public abstract long getLink(long state, int tidx);

	/**
	 * Assign link to node during SCC search. If a link has already been
	 * assigned to the node, does nothing by simply returning the existing link.
	 * Otherwise, add &lt;node, link&gt; into the table and return -1. The link
	 * overwrites the previous value of elem (file pointer into nodes_N) in the
	 * nodePtrTable.
	 * <p>
	 * The link has to be in the range [{@link AbstractDiskGraph#MAX_PTR},
	 * {@link AbstractDiskGraph#MAX_LINK}). {AbstractDiskGraph#MAX_LINK} is used
	 * to exclude nodes from being explored by SCC search twice (see
	 * {@link AbstractDiskGraph#setMaxLink(long, int)}.
	 * 
	 * @param state
	 *            The state's fingerprint
	 * @param tidx
	 *            The corresponding tableau index
	 */
	public abstract long putLink(long state, int tidx, long link);

	/**
	 * Assigns the maximum possible link number to the given node &lt;state,
	 * tidx&gt;. This results in that the node is skipped/ignored if it turns up
	 * as a node during SCC's depth-first-search.
	 * 
	 * @param state
	 *            The state's fingerprint
	 * @param tidx
	 *            The corresponding tableau index
	 */
	public abstract void setMaxLink(long state, int tidx);

	/* End link information for SCC search */

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
	 * @return The amount of distinguishable GraphNodes in this graph. Note that
	 *         the size can be incorrect if an initial state has only been added
	 *         via {@link AbstractDiskGraph#addInitNode(long, int)} only but not
	 *         via {@link AbstractDiskGraph#addNode(GraphNode)}.
	 */
	public abstract long size();
	
	/**
	 * @return The size of both disk files (ptrs and nodes) measured in bytes.
	 *         Can be incorrect during short periods when the graph is being
	 *         recreated ({@link #makeNodePtrTbl()}) or nodes are read from
	 *         disk ({@link #getNodeFromDisk(long, int, long)}). It is up to
	 *         the caller to take this into account.
	 * @throws IOException
	 */
	public long getSizeOnDisk() throws IOException {
		return this.nodePtrRAF.length() + this.nodeRAF.length();
	}
	
	public long getSizeAtLastCheck() {
		return sizeAtCheck;
	}

	public void recordSize() {
		this.sizeAtCheck = size();
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

		public String toString() {
			return "NodeRAFRecord [fp=" + fp + ", tidx=" + tidx + "]";
		}

		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + (int) (fp ^ (fp >>> 32));
			result = prime * result + tidx;
			return result;
		}

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
