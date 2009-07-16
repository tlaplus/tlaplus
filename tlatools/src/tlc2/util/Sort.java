// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import util.WrongInvocationException;

/**
 * The <code>Sort</code> class provides sorting methods.<P>
 *
 * For the quicksort version, the median-of-three method is
 * used to select the pivot element. See "Algorithms in C",
 * Third edition, by Robert Sedgewick, sections 7.1 and 7.5
 * (quick sort) and section 6.3 (insertion sort).
 */

public class Sort {
  private static final int InsertionSize = 16;

  /* Sort the subarray of array A from start to finish inclusive. */
  private static void insertionSort(Comparable[] A, int start, int finish) {
    Comparable t;
    int j;

    // Use the smallest element as a sentinel
    for (int i = start + 1; i <= finish; i++) {
      if (A[start].compareTo(A[i]) > 0) {
	t = A[start];
	A[start] = A[i];
	A[i] = t;
      }
    }
    for (int i = start+2; i <= finish; i++) {
      t = A[i];
      for (j = i - 1; A[j].compareTo(t) > 0; j--) {
	A[j+1] = A[j];
      }
      A[j+1] = t;
    }
  }

  /*
   * Merges the subarray of array A from start1 to finish1 with the
   * subarray from finish1+1 to finish2, in place.
   */
  private static void merge(Comparable A[], int start1, int finish1, int finish2) {
    if (finish2 < finish1) {
        throw new WrongInvocationException("Cannot merge subarrays where finish2 < finish1.");
    }
    int i = start1;
    int j = finish1+1;
    int k = 0;
    Comparable Atmp[] = new Comparable[finish2-start1+1]  ;

    while (i <= finish1 && j <= finish2) {
      if (A[j].compareTo(A[i]) >= 0) {
	Atmp[k] = A[i];
	i++;
      } else {
	Atmp[k] = A[j];
	j++;
      }
      k++;
    }
    if (i == finish1+1) {
      for (;j<=finish2; j++) {
	Atmp[k] = A[j];
	k++;
      }
    } else {
      for (; i<=finish1; i++) {
	Atmp[k] = A[i];
	k++;
      }
    }
    for (k = 0; k < finish2-start1+1; k++) {
      A[start1+k] = Atmp[k];
    }
  }

  /* Sort the subarray of array A from start to finish inclusive. */
  public static void mergeSort(Comparable A[], int start, int finish) {
    int i = start, j, s, k, l, top;
    boolean done = false;

    while (!done) {
      // i is the start of a segment of size InsertionSize and j the end,
      // but we have to make sure not to go past the end of the array.
      if (i+InsertionSize <= finish)
	j = i+InsertionSize-1;
      else {
	j = finish;
	done = true;
      }
      insertionSort(A,i,j);
      i += InsertionSize;
    }

    s = InsertionSize;
    while (s <= finish-start) {
      k = start;
      l = k+s;
      for (; l <= finish;) {
	if (finish < l+s-1) {
	  top = finish;
	}
	else {
	  top = l+s-1;
	}
	merge(A,k,l-1,top);
	k = l + s; 
	l = k + s;
      }
      s += s;
    }
  }

  /* Sort the <code>Comparable</code>s in <code>a</code>. */
  public static void sortArray(Comparable[] a, int lo, int hi) {
    quickSort(a, lo, hi);
    // mergeSort(a,lo,hi);
    // insertionSort(a, lo, hi);
  }

  /* Sort the <code>Comparable</code>s in <code>a</code> and remove duplicates. */
  public static int sortArrayNoDups(Comparable[] a, int lo, int hi) {
    sortArray(a, lo, hi);
    int last = lo;
    for (int i = lo+1; i <= hi; i++) {
      if (a[last].compareTo(a[i]) != 0) {
	a[++last] = a[i];
      }
    }
    return (lo <= hi) ? last : hi;
  }

  /* Sort the elements of "buff" in the closed interval "[lo, hi]". */
  private static void quickSort(Comparable[] a, int lo, int hi) {
    if (hi - lo <= InsertionSize) {
      insertionSort(a, lo, hi);
    }
    else {
      int mid = (lo + hi) / 2;
      Comparable t = a[mid]; a[mid] = a[hi-1]; a[hi-1] = t;

      // sort three elements a[lo], a[hi-1], a[hi]
      if (a[lo].compareTo(a[hi-1]) > 0) {
	t = a[lo]; a[lo] = a[hi-1]; a[hi-1] = t;
      }
      if (a[lo].compareTo(a[hi]) > 0) {
	t = a[lo]; a[lo] = a[hi]; a[hi] = t;
      }
      if (a[hi-1].compareTo(a[hi]) > 0) {
	t = a[hi-1]; a[hi-1] = a[hi]; a[hi] = t;
      }
    
      // partition
      int i = partition(a, lo+1, hi-1);
    
      // sort subfiles recursively
      quickSort(a, lo, i-1);
      quickSort(a, i+1, hi);
    }
  }
  
  private static int partition(Comparable[] a, int lo, int hi) {
    int i = lo - 1, j = hi;
    Comparable value = a[hi];
    
    while (true) {
      while (value.compareTo(a[++i]) > 0) { /*SKIP*/ }
      while (a[--j].compareTo(value) > 0) { if (j == lo) break; }
      if (i >= j) break;
      Comparable t = a[i]; a[i] = a[j]; a[j] = t;
    }
    Comparable t = a[i]; a[i] = a[hi]; a[hi] = t;
    return i;
  }
      
  /* Sort the <code>long</code>s in <code>a</code>. */
  public static void LongArray(long[] a, int n) {
    int hi = n - 1;
    quickSort(a, 0, hi);
    insertionSort(a, 0, hi);
  }

  /* Sort the elements of "buff" in the closed interval
     "[lo, hi]". */
  private static void quickSort(long[] a, int lo, int hi) {
    if (hi - lo <= InsertionSize) return;
    int mid = (lo + hi) / 2;
    long t = a[mid]; a[mid] = a[hi-1]; a[hi-1] = t;

    // sort three elements a[lo], a[hi-1], a[hi]
    if (a[lo] > a[hi-1]) {
      t = a[lo]; a[lo] = a[hi-1]; a[hi-1] = t;
    }
    if (a[lo] > a[hi]) {
      t = a[lo]; a[lo] = a[hi]; a[hi] = t;
    }
    if (a[hi-1] > a[hi]) {
      t = a[hi-1]; a[hi-1] = a[hi]; a[hi] = t;
    }
        
    // partition
    int i = partition(a, lo+1, hi-1);
        
    // sort subfiles recursively
    quickSort(a, lo, i-1);
    quickSort(a, i+1, hi);
  }
    
  private static int partition(long[] a, int lo, int hi) {
    int i = lo - 1, j = hi;
    long value = a[hi];
    while (true) {
      while (a[++i] < value) /*SKIP*/;
      while (value < a[--j]) { if (j == lo) break; }
      if (i >= j) break;
      long t = a[i]; a[i] = a[j]; a[j] = t;
    }
    long t = a[i]; a[i] = a[hi]; a[hi] = t;
    return i;
  }
    
  private static void insertionSort(long[] a, int lo, int hi) {
    // first, put smallest elt in a[lo] as sentinel
    for (int i = lo + 1; i <= hi; i++) {
      if (a[lo] > a[i]) {
	long t = a[lo]; a[lo] = a[i]; a[i] = t;
      }
    }
        
    // body of insertion sort
    for (int i = lo + 2; i <= hi; i++) {
      int j = i;
      long value = a[i];
      while (value < a[j-1]) {
	a[j] = a[j-1];
	j--;
      }
      a[j] = value;
    }
  }

}


