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

	private final LongBuffer lBuf;
	private final SortedSet<Long> collisionBucket;
	/**
	 * Number of elements in the buffer
	 */
	private long bufferElements;
	/**
	 * Total amount of elements in both the buffer as well as the collisionBucket. 
	 */
	private final long totalElements;
	/**
	 * The logical position is the position inside the {@link LongBuffer} and
	 * thus reflects a fingerprints
	 */
	private int logicalPosition = 0;
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

	public ByteBufferIterator(final ByteBuffer aBuffer, SortedSet<Long> collisionBucket, long expectedElements) {
		aBuffer.position(0);
		
		this.totalElements = expectedElements;
		this.lBuf = aBuffer.asLongBuffer();
		
		this.collisionBucket = collisionBucket;
		this.bufferElements = expectedElements - this.collisionBucket.size();
	}

    /**
     * Returns the next element in the iteration.
     *
     * @return the next element in the iteration.
     * @exception NoSuchElementException iteration has no more elements.
     */
	public long next() {
		long result = -1l;

		if (cache < 0L && bufferElements > 0) {
			result = getNextFromBuffer();
			bufferElements--;
		} else {
			result = cache;
			cache = -1L;
		}

		if (!collisionBucket.isEmpty()) {
			long first = collisionBucket.first();
			if (result > first || result == -1L) {
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
		sortNextBucket();
		
		long l = lBuf.get(logicalPosition);
		if (l > 0L) {
			lBuf.put(logicalPosition++, l | 0x8000000000000000L);
			return l;
		}
		
		while ((l = lBuf.get(logicalPosition)) <= 0L && logicalPosition < lBuf.capacity()) {
			// increment position to next bucket and recursively call self
			logicalPosition = (logicalPosition + DiskFPSet.InitialBucketCapacity) & 0x7FFFFFF0;
			sortNextBucket();
		}
		
		if (l > 0L) {
			lBuf.put(logicalPosition++, l | 0x8000000000000000L);
			return l;
		}
		throw new NoSuchElementException();
	}

	// sort the current logical bucket if we reach the first slot of the
	// bucket
	private void sortNextBucket() {
		if (logicalPosition % DiskFPSet.InitialBucketCapacity == 0) {
			long[] longBuffer = new long[DiskFPSet.InitialBucketCapacity];
			int i = 0;
			for (; i < DiskFPSet.InitialBucketCapacity; i++) {
				long l = lBuf.get(logicalPosition + i);
				if (l <= 0L) {
					break;
				} else {
					longBuffer[i] = l;
				}
			}
			Arrays.sort(longBuffer, 0, i);
			for (int j = 0; j < i; j++) {
				lBuf.put(logicalPosition + j, longBuffer[j]);
			}
		}
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
		return readElements < totalElements;
	}

	/**
	 * @return The number of element read with {@link TLCIterator#next()} since
	 *         the creation of this instance.
	 */
	public long reads() {
		return readElements;
	}
	
	/**
	 * @return The last element in the iteration.
     * @exception NoSuchElementException if iteration is empty.
	 */
	public long getLast() {
		int tmpLogicalPosition = logicalPosition;
		logicalPosition = this.lBuf.capacity() - DiskFPSet.InitialBucketCapacity;
		sortNextBucket();

		// reverse the current bucket to obtain last element
		long l = 1L;
		while ((l = lBuf.get(logicalPosition-- + DiskFPSet.InitialBucketCapacity - 1)) <= 0L) {
			if (((logicalPosition - DiskFPSet.InitialBucketCapacity) & 0x7FFFFFF0) == 0) {
				sortNextBucket();
			}
		}
		
		if (l > 0L) {
			logicalPosition = tmpLogicalPosition;
			return l;
		}
		throw new NoSuchElementException();
	}
}
