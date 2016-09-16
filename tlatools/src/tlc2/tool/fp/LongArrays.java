// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

public class LongArrays {

	/**
	 * Sorts the specified range of the array.
	 */
	public static void sort(final LongArray a, final long left, final long right, final LongComparator cmp,
			final PivotSelector ps) {
		final long size = a.size();

		// Use insertion sort for small arrays.
		if (size < 47) {
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
		} else {
			// ++++++ Quicksort ++++++//
			final long pivotPos = ps.getPos(a, left, right);
			final long pivot = a.get(pivotPos);

			long i = left;
			long j = right;
			while (i <= j) {
				while (cmp.compare(a.get(i % size), i % size, pivot, pivotPos % size) <= 0 && i < right) {
					i++;
				}
				while (cmp.compare(a.get(j % size), j % size, pivot, pivotPos % size) >= 0 && j > left) {
					j--;
				}

				if (i < j) {
					// Only swap when needed.
					a.swap(i % size, j % size);
					i++;
					j--;
				} else if (i == j) {
					i++;
					j--;
				}
			}
			// Recurse.
			if (left < i) {
				sort(a, left, j, cmp, ps);
			}
			if (i < right) {
				sort(a, i, right, cmp, ps);
			}
		}
	}
	
	public static class LongComparator {
		public int compare(long lo, long loPos, long hi, long hiPos) {
			return 0;
		}
	}
	
	public static class PivotSelector {
		/**
		 * @return The position of the selected pivot element in a.
		 */
		public long getPos(LongArray a, long left, long right) {
			return ((left + right) >>> 1) % a.size(); // The midpoint
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
