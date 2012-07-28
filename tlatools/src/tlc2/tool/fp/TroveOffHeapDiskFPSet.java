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
		this.collisionBucket = new TLongCollisionBucket();
	}
	
	public class TLongCollisionBucket extends CollisionBucket {
		/**
		 * A bucket containing collision elements
		 */
		private final TLongSet set;
		private long[] array;
		private int idx = 0;
		
		public TLongCollisionBucket() {
			this.set = new TLongHashSet();
		}
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#prepareForFlush()
		 */
		@Override
		public void prepareForFlush() {
			this.idx = 0; // Reset idx every time flush is called
			this.array = this.set.toArray();
			this.set.clear(); // might want to call System.gc() here
			Sort.LongArray(this.array, this.array.length);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#remove(long)
		 */
		@Override
		public void remove(long fp) {
			this.array[idx++] = -1L;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#first()
		 */
		@Override
		public long first() {
			return this.array[idx];
		}
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#last()
		 */
		@Override
		public long last() {
			return this.array[array.length - 1];
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#isEmpty()
		 */
		@Override
		public boolean isEmpty() {
			return !(idx <= array.length - 1);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#add(long)
		 */
		@Override
		public void add(long fp) {
			set.add(fp);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#contains(long)
		 */
		@Override
		public boolean contains(long fp) {
			return set.contains(fp);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.OffHeapDiskFPSet.CollisionBucket#size()
		 */
		@Override
		public long size() {
			return set.size();
		}
	}
}
