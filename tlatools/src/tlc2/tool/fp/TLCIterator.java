package tlc2.tool.fp;

import java.util.NoSuchElementException;

import tlc2.output.EC;
import util.Assert;

public class TLCIterator {

	private final long[][] buff;
	/**
	 * Index pointing to the current bucket in the first level of
	 * {@link TLCIterator#buff}
	 */
	private int firstIdx = 0;
	/**
	 * Index pointing to the current element in the current bucket which is the
	 * second level of {@link TLCIterator#buff}
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

	/**
	 * @param buff an [][] with null elements on the second level.
	 */
	public TLCIterator(final long[][] buff) {
		this.buff = buff;
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
		
		// firstIdx within buff[].length
		if (firstIdx < buff.length) {
			long[] bucket = buff[firstIdx];
			// secondIdx within bucket[].length and with valid elements in current bucket 
			if (bucket != null && secondIdx < bucket.length && bucket[secondIdx] > 0) {
				return true;
			// we might have reached a null or negative range in buff[] -> skip it until
			// we reach a non-null and non negative bucket or we get to the end of buff[]
			} else {
				for (int i = firstIdx + 1; i < buff.length; i++) {
					if (buff[i] != null && buff[i].length > 0 && buff[i][0] > 0) {
						return true;
					}
				}
			}
		}
		return false;
	}

    /**
     * Returns the next element in the iteration.
     *
     * @return the next element in the iteration.
     * @exception NoSuchElementException iteration has no more elements.
     */
	public long next() {
		long result = -1l;
		
		// at least one more element in current bucket
		if (firstIdx < buff.length) {
			long[] bucket = buff[firstIdx];
			if (bucket != null && secondIdx < bucket.length && bucket[secondIdx] > 0) {
				result = bucket[secondIdx];
				bucket[secondIdx] |= 0x8000000000000000L;
				secondIdx++;
			} else {
				for (int i = firstIdx + 1; i < buff.length && result == -1L; i++) {
					if (buff[i] != null && buff[i].length > 0 && buff[i][0] > 0) {
						firstIdx = i;
						secondIdx = 0;
						result = buff[firstIdx][secondIdx];
						buff[firstIdx][secondIdx] |= 0x8000000000000000L;
						secondIdx++;
						break; // redundant to "result == -1L" in for loop
					}
				}
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

	/**
	 * @return The last element in the iteration.
     * @exception NoSuchElementException if iteration is empty.
	 */
	public long getLast() {
		int len = buff.length - 1;
		long[] bucket = buff[len];

		// find last bucket containing elements, buff elements might be null if
		// no fingerprint for such an index has been added to the DiskFPSet
		while (bucket == null) {
			bucket = buff[--len];
		}
		
		// find last element > 0 in bucket
		for (int i = bucket.length - 1; i >= 0 ;i--) {
			if (bucket[i] > 0) {
				return bucket[i];
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
}
