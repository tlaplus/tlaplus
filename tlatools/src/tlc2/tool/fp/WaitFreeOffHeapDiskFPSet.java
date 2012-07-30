// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.rmi.RemoteException;
import java.util.Iterator;
import java.util.SortedSet;
import java.util.TreeSet;

import org.cliffc.high_scale_lib.NonBlockingHashSet;

@SuppressWarnings("serial")
public class WaitFreeOffHeapDiskFPSet extends OffHeapDiskFPSet {
	
	protected WaitFreeOffHeapDiskFPSet(long maxInMemoryCapacity) throws RemoteException {
		this(maxInMemoryCapacity, 0);
	}
	
	protected WaitFreeOffHeapDiskFPSet(long maxInMemoryCapacity, int prefixBits) throws RemoteException {
		super(maxInMemoryCapacity, prefixBits);
		this.collisionBucket = new WaitFreeCollisionBucket();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.OffHeapDiskFPSet#csLookup(long)
	 */
	@Override
	protected boolean csLookup(long fp) {
		return this.collisionBucket.contains(fp);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.OffHeapDiskFPSet#csInsert(long)
	 */
	@Override
	protected boolean csInsert(long fp) {
		return this.collisionBucket.add(fp);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.OffHeapDiskFPSet#getCollisionBucketCnt()
	 */
	@Override
	public long getCollisionBucketCnt() {
		// WaitFree impl does not need locks like super class 
		return collisionBucket.size();
	}

	public class WaitFreeCollisionBucket extends CollisionBucket {
		private final NonBlockingHashSet<Long> set;
		private final SortedSet<Long> sortedSet;

		public WaitFreeCollisionBucket() {
			this.set = new NonBlockingHashSet<Long>();
			this.sortedSet = new TreeSet<Long>();
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#prepareForFlush()
		 */
		@Override
		public void prepareForFlush() {
			Iterator<Long> itr = this.set.iterator();
			while(itr.hasNext()) {
				Long l = itr.next();
				this.set.remove(l);
				this.sortedSet.add(l);
			}
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#remove(long)
		 */
		@Override
		public void remove(long fp) {
			this.sortedSet.remove(fp);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#first()
		 */
		@Override
		public long first() {
			return this.sortedSet.first();
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#last()
		 */
		@Override
		public long last() {
			return this.sortedSet.last();
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#isEmpty()
		 */
		@Override
		public boolean isEmpty() {
			return this.sortedSet.isEmpty();
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#add(long)
		 */
		@Override
		public boolean add(long fp) {
			return this.set.add(fp);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#contains(long)
		 */
		@Override
		public boolean contains(long fp) {
			return this.set.contains(fp);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#size()
		 */
		@Override
		public long size() {
			return this.set.size();
		}
	}
}
