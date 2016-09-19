// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

public class LongArrays {

	/**
	 * Sorts the specified range of the array.
	 */
	public static void sort(final LongArray a, final long left, final long right, final LongComparator cmp) {
		final long size = a.size();

		//+++++++ Insertions sort +++++++//
		for (long i = left, j = i; i < right; j = ++i) {
			final long lo = (i + 1) % size;
			final long ai = a.get(lo);
			while (cmp.compare(ai, lo, a.get(j % size), j % size) <= -1) {
				a.set((j + 1) % size, a.get(j % size));
				if (j-- == left) {
					break;
				}
			}
			a.set((j + 1) % size, ai);
		}
	}
	
	public static class LongComparator {
		public int compare(long lo, long loPos, long hi, long hiPos) {
			return 0;
		}
	}

	/**
	 * DOES NOT HANDLE LONG ARRAYS LARGER THAN INTEGER.MAX_VALUE
	 */
	public static long[] toArray(final LongArray array) {
		final long[] res = new long[(int) array.size()];
		for (int i = 0; i < array.size(); i++) {
			long l = array.get(i);
			res[i] = l;
		}
		return res;
	}
}
