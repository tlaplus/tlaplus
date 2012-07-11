package tlc2.tool.fp;

import java.nio.ByteBuffer;
import java.nio.LongBuffer;
import java.util.Arrays;
import java.util.NoSuchElementException;
import java.util.SortedSet;

import tlc2.output.EC;
import tlc2.tool.fp.MSBDiskFPSet.TLCIterator;
import util.Assert;

public class ByteBufferIterator {
	private static final int BUCKET_SIZE_IN_BYTES = DiskFPSet.InitialBucketCapacity * DiskFPSet.LongSize;

	private final ByteBuffer buff;
	private final LongBuffer lBuf;
	private final SortedSet<Long> collisionBucket;
	private final long expectedElements;
	/**
	 * Index pointing to the current bucket in the first level
	 */
	private int firstIdx = 0;
	/**
	 * Index pointing to the current element in the current bucket which is the
	 * second level
	 */
	private int secondIdx = 0;
	/**
	 * Used to verify that the elements we hand out are strictly monotonic
	 * increasing.
	 */
	private long previous = -1l;
	/**
	 * Number of elements read with next()
	 */
	private long readElements = 0L;

	private long cache = -1L;
	private CacheEntry ce = new CacheEntry();


	public ByteBufferIterator(final ByteBuffer aBuffer, SortedSet<Long> collisionBucket, long expectedElements) {
		this.buff = aBuffer;
		this.buff.position(0);
		this.expectedElements = expectedElements;
		lBuf = aBuffer.asLongBuffer();
		this.collisionBucket = collisionBucket;
		System.out.println(this.collisionBucket.size());
	}

    /**
     * Returns the next element in the iteration.
     *
     * @return the next element in the iteration.
     * @exception NoSuchElementException iteration has no more elements.
     */
	public long next() {
		long result = -1l;

		if (cache < 0L) {
			result = getNextFromBuffer();
		} else {
			result = cache;
			cache = -1L;
		}
		
		if (!collisionBucket.isEmpty()) {
			long first = collisionBucket.first();
			if (result > first) {
				collisionBucket.remove(first);
				cache = result;
				result = first;
			}
		}
		
		// adhere to the general Iterator contract to fail fast and not hand out
		// meaningless values
		if (result == -1L) {
			throw new NoSuchElementException();
		}
		
		// hand out strictly monotonic increasing elements
		Assert.check(previous < result, EC.GENERAL);
		previous = result;
		
		// maintain read statistics
		readElements++;
		
		return result;
	}

	private long getNextFromBuffer() {
		long result = -1l;
		// at least one more element in current bucket
		if (firstIdx < buff.capacity()) {
			long[] bucket = getBucketCached(firstIdx);
			if (bucket != null && secondIdx < bucket.length && bucket[secondIdx] > 0) {
				result = bucket[secondIdx];
				bucket[secondIdx] |= 0x8000000000000000L;
				secondIdx++;
			} else {
				for (int i = firstIdx + BUCKET_SIZE_IN_BYTES; i < buff.capacity() && result == -1L; i += BUCKET_SIZE_IN_BYTES) {
					bucket = getBucketCached(i);
					if (bucket != null && bucket.length > 0 && bucket[0] > 0) {
						firstIdx = i;
						secondIdx = 0;
						result = bucket[secondIdx];
						bucket[secondIdx] |= 0x8000000000000000L;
						secondIdx++;
						break; // redundant to "result == -1L" in for loop
					}
				}
			}
		}
		return result;
	}

    /**
     * Returns <tt>true</tt> if the iteration has more elements. (In other
     * words, returns <tt>true</tt> if <tt>next</tt> would return an element
     * rather than throwing an exception.)
     *
     * @return <tt>true</tt> if the iterator has more elements.
     */
	public boolean hasNext() {
		// hasNext does not move the indices at all!
		
		if (firstIdx < buff.capacity()) {
			long[] bucket = getBucket(firstIdx);
			// secondIdx within bucket[].length and with valid elements in current bucket 
			if (bucket != null && secondIdx < bucket.length && bucket[secondIdx] > 0) {
				return true;
			// we might have reached a null or negative range in buff[] -> skip it until
			// we reach a non-null and non negative bucket or we get to the end of buff[]
			} else {
				for (int i = firstIdx + BUCKET_SIZE_IN_BYTES; i < buff.capacity(); i += BUCKET_SIZE_IN_BYTES) {
					bucket = getBucket(i);
					if (bucket != null && bucket.length > 0 && bucket[0] > 0) {
						return true;
					}
				}
			}
		}
		
		boolean empty = collisionBucket.isEmpty();
		if (empty) {
//			Assert.check(readElements == expectedElements ,EC.GENERAL);
			return false;
		} else {
			return true;
		}
	}

	/**
	 * @return The last element in the iteration.
     * @exception NoSuchElementException if iteration is empty.
	 */
	public long getLast() {		
		final int capacity = this.buff.capacity();

		// get last bucket, sort and read last slot (max fp)
		long[] bucket = getBucket(capacity - BUCKET_SIZE_IN_BYTES);;

		// find last bucket containing elements, buff elements might be null if
		// no fingerprint for such an index has been added to the DiskFPSet
		int j = 2;
		while (bucket == null) {
			bucket = getBucket(capacity - (BUCKET_SIZE_IN_BYTES * j++));
		}
		
		// find last element > 0 in bucket
		for (int i = bucket.length - 1; i >= 0 ;i--) {
			if (bucket[i] > 0) {
				return bucket[i] >= collisionBucket.last() ? bucket[i] : collisionBucket.last();
			}
		}
		throw new NoSuchElementException();
	}
	
	/**
	 * @return The number of element read with {@link TLCIterator#next()} since
	 *         the creation of this instance.
	 */
	public long reads() {
		return readElements;
	}
	
	public void close() {
		if (ce.key >= 0 && ce.value != null) {
			lBuf.position(ce.key / DiskFPSet.LongSize);
			lBuf.put(ce.value);
		}
	}
	
	/**
	 * @param offset
	 * @return <code>null</code> if the bucket at offset contains only <= 0L
	 *         values, a _sorted_ bucket otherwise.
	 */
	private long[] getBucket(int offset) {
		this.buff.position(offset);
		
		long[] longBuffer = new long[DiskFPSet.InitialBucketCapacity];
		for (int i = 0; i < DiskFPSet.InitialBucketCapacity; i++) {
			long l = this.buff.getLong();
			if (l <= 0L && i == 0) {
				return null;
			} else if (l <= 0L) {
				Arrays.sort(longBuffer, 0, i);
				return longBuffer;
			} else {
				longBuffer[i] = l;
			}
		}
		Arrays.sort(longBuffer);
		return longBuffer;
	}
	
	/**
	 * @param offset
	 * @return <code>null</code> if the bucket at offset contains only <= 0L
	 *         values, a _sorted_ bucket otherwise.
	 */
	private long[] getBucketCached(int offset) {
		if (offset == ce.key) {
			return ce.value;
		} else if (ce.key >= 0 && offset > ce.key && ce.value != null) {
			lBuf.position(ce.key / DiskFPSet.LongSize);
			lBuf.put(ce.value);
		}

		long[] bucket = getBucket(offset);
		ce.key = offset;
		ce.value = bucket;
		return bucket;
	}
	
	private static class CacheEntry {
		public long[] value;
		public int key = -1;
	}
}
