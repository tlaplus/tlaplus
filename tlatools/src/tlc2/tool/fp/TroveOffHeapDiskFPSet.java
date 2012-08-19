// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import gnu.trove.set.TLongSet;
import gnu.trove.set.hash.TLongHashSet;

import java.rmi.RemoteException;

import tlc2.util.Sort;

@SuppressWarnings("serial")
public class TroveOffHeapDiskFPSet extends OffHeapDiskFPSet implements FPSetStatistic {

	protected TroveOffHeapDiskFPSet(long maxInMemoryCapacity) throws RemoteException {
		this(maxInMemoryCapacity, 0);
	}
	
	protected TroveOffHeapDiskFPSet(final long maxInMemoryCapacity, int preBits) throws RemoteException {
		super(maxInMemoryCapacity, preBits);
		final int capacity = (int) (maxTblCnt * COLLISION_BUCKET_RATIO);
		this.collisionBucket = new TLongCollisionBucket(capacity);
	}
	
	public class TLongCollisionBucket implements CollisionBucket {
		/**
		 * A bucket containing collision elements
		 */
		private final TLongSet set;
		private long[] array;
		private int idx = 0;
		
		public TLongCollisionBucket(int capacity) {
			this.set = new TLongHashSet(capacity);
		}
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#prepareForFlush()
		 */
		public void prepareForFlush() {
			this.idx = 0; // Reset idx every time flush is called
			this.array = this.set.toArray();
			this.set.clear(); // might want to call System.gc() here
			Sort.LongArray(this.array, this.array.length);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#remove(long)
		 */
		public void remove(long fp) {
			this.array[idx++] = -1L;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#first()
		 */
		public long first() {
			return this.array[idx];
		}
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#last()
		 */
		public long last() {
			return this.array[array.length - 1];
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#isEmpty()
		 */
		public boolean isEmpty() {
			return !(idx <= array.length - 1);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#add(long)
		 */
		public boolean add(long fp) {
			return set.add(fp);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#contains(long)
		 */
		public boolean contains(long fp) {
			return set.contains(fp);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#size()
		 */
		public long size() {
			return set.size();
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#clear()
		 */
		public void clear() {
			array = null;
			set.clear();
		}
	}
}
