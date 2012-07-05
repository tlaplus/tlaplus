package tlc2.tool.fp;

import java.util.NoSuchElementException;

import tlc2.output.EC;
import util.Assert;

//TODO skip null buckets
public class TLCIterator {

	private final long[][] buff;
	private int firstIdx = 0;
	private int secondIdx = 0;
	private long previous = -1l;
	/**
	 * Number of elements read with next()
	 */
	private long readElements = 0l;

	/**
	 * @param buff an [][] with null elements on the second level.
	 */
	public TLCIterator(long[][] buff) {
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
			if (secondIdx < bucket.length && bucket[secondIdx] > 0) {
				return true;
			// at the end of current bucket, skipping to next one 
			} else if (firstIdx + 1 < buff.length && buff[firstIdx + 1] != null) {
				bucket = buff[firstIdx + 1];
				return bucket != null && bucket.length > 0 && bucket[0] > 0;
			// we might have reached a null range in buff[] -> skip it until
			// we reach a non-null bucket or we get to the end of buff[]
			} else {
				for (int i = firstIdx + 1; i < buff.length; i++) {
					if (buff[i] != null) {
						bucket = buff[i];
						return bucket.length > 0 && bucket[0] > 0;
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
		if (firstIdx <= buff.length - 1) {
			long[] bucket = buff[firstIdx];
			if (secondIdx < bucket.length && bucket[secondIdx] > 0) {
				result = bucket[secondIdx];
				bucket[secondIdx] |= 0x8000000000000000L;
				secondIdx++;
			} else if (firstIdx + 1 < buff.length && buff[firstIdx + 1] != null) {
				firstIdx++;
				secondIdx = 0;
				result = buff[firstIdx][secondIdx];
				buff[firstIdx][secondIdx] |= 0x8000000000000000L;
				secondIdx++;
			} else {
				for (int i = firstIdx + 1; i < buff.length && result == -1L; i++) {
					if (buff[i] != null) {
						firstIdx = i;
						secondIdx = 0;
						result = buff[firstIdx][secondIdx];
						buff[firstIdx][secondIdx] |= 0x8000000000000000L;
						secondIdx++;
						break;
					}
				}
			}
		}
		
		if (result == -1L) {
			throw new NoSuchElementException();
		}
		
		Assert.check(previous < result, EC.GENERAL);
		previous = result;
		
		readElements++;
		
		return result;
	}

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
	
	public long reads() {
		return readElements;
	}
}
