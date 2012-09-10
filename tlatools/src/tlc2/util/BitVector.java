// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:26 PST by lamport
//      modified on Thu Nov 29 21:53:11 PST 2001 by yuanyu
package tlc2.util;

/** A <code>BitVector</code> is an ordered list of bits
    of potentially unbounded size. The index of the first
    bit in a bit vector is 0.<p>
    
    This class is unmonitored; it is the responsibility
    of clients to guarantee thread safety. The read-only
    methods are <code>get</code> and <code>iterator</code>.

    Written by Allan Heydon and Marc Majork
*/

import java.io.IOException;
import java.io.Serializable;

public class BitVector implements Serializable {

  private static final long serialVersionUID = 901734230891583097L;
  private long[] word;                   // words of this bit vector

  public BitVector() { this.word = null; }
  
  /**
   * Constructor for a new bit vector that is expected to contain bits
   * with indices 0 through <code>initCapacity-1</code>.
   */
  public BitVector(int initCapacity) {
    int len = (initCapacity == 0) ? 0 : ((initCapacity - 1)/64 + 1);
    this.word = new long[len];
  }
  
	/**
	 * Constructor for a new bit vector that is expected to contain bits with
	 * indices 0 through <code>initCapacity-1</code>. All bits are initially set
	 * to <code>true</code>
	 */
	public BitVector(int initCapacity, boolean initValue) {
		int len = (initCapacity == 0) ? 0 : ((initCapacity - 1) / 64 + 1);
		this.word = new long[len];
		if (initValue) {
			set(0, len);
		}
	}
   
  /** Initialize this bit vector to be a copy of <code>bv</code>. */
  public BitVector(BitVector bv) {
    int len = bv.word.length;
    this.word = new long[len];
    System.arraycopy(bv.word, 0, this.word, 0, len);
  }

  public boolean equals(Object o) {
    if (!(o instanceof BitVector)) return false;
    BitVector other = (BitVector)o;
    int minLen = Math.min(this.word.length, other.word.length);
    for (int i = 0; i < minLen; i++) {
      if (this.word[i] != other.word[i]) return false;
    }
    if (this.word.length != other.word.length) {
      int maxLen = Math.max(this.word.length, other.word.length);
      long[] tail = (maxLen == this.word.length) ? this.word : other.word;
      for (int i = minLen; i < maxLen; i++) {
	if (tail[i] != 0L) return false;
      }
    }
    return true;
  }

  public int hashCode() {
    int res = 0;
    for (int i = 0; i < this.word.length; i++) {
      long w = this.word[i];
      if (w != 0) {
	res ^= (int)(w & 0xffffL);
	res ^= (int)(w >>> 32);
      }
    }
    return res;
  }

  /** Reset all of this bit vector's bits. */
  public void clear() {
    for (int i = 0; i < this.word.length; i++) {
      this.word[i] = 0L;
    }
  }
    
  /** Return the bit at index <code>i</code>. */
  public boolean get(int i) {
    int wd = i / 64;
    if (wd >= this.word.length) return false;
    int bit = i % 64;
    return (this.word[wd] & (1L << bit)) != 0L;
  }
    
  /** Set the bit at index <code>i</code> to <code>true</code>. */
  public void set(int i) {
    int wd = i / 64;
    if (wd >= this.word.length) this.grow(wd);
    int bit = i % 64;
    this.word[wd] |= (1L << bit);
  }
    
  /** Set all the bits with indices in the closed interval
      <code>[lo, hi]</code>. */
  public void set(int lo, int hi) {
    int lwd = lo / 64;
    int hwd = hi / 64;
    if (hwd >= this.word.length) this.grow(hwd);
    int lbit = lo % 64;
    int hbit = hi % 64;
    if (lwd < hwd) {
      for (int i = lwd+1; i < hwd; i++) {
	this.word[i] = -1L;
      }
      this.word[lwd] = (-1L << lbit);
      this.word[hwd] = (-1L >>> (63-hbit));
    }
    else {
      if (lo <= hi) {
	this.word[lwd] = (-1L << lbit) & (-1L >>> (63-hbit));
      }
    }
  }
  
	/**
	 * @return The number of bits set true
	 */
	public int trueCnt() {
		int res = 0;
		for (int i = 0; i < this.word.length * 64; i++) {
			// addr in long[]
			int wd = i / 64;
			// addr in long[x]
			int bit = i % 64;
			if ((this.word[wd] & (1L << bit)) != 0L) {
				res++;
			}
		}
		return res;
	}
    
  /** Set the bit at index <code>i</code> to <code>false</code>. */
  public void reset(int i) {
    int wd = i / 64;
    if (wd >= this.word.length) this.grow(wd);
    int bit = i % 64;
    this.word[wd] &= ~(1L << bit);
  }
    
  /** Set the bit at index <code>i</code> to <code>val</code>. */
  public void set(int i, boolean val) {
    int wd = i / 64;
    if (wd >= this.word.length) this.grow(wd);
    int bit = i % 64;
    if (val) {
      this.word[wd] |= (1L << bit);
    } else {
      this.word[wd] &= ~(1L << bit);
    }
  }

  /** Write the bit vector to a file. */
  public void write(BufferedRandomAccessFile raf) throws IOException {
    int len = this.word.length;
    raf.writeNat(len);
    for (int i = 0; i < len; i++) {
      raf.writeLong(this.word[i]);
    }
  }

  /** Read a bit vector from a file */
  public void read(BufferedRandomAccessFile raf) throws IOException {
    int len = raf.readNat();
    this.word = new long[len];
    for (int i = 0; i < len; i++) {
      this.word[i] = raf.readLong();
    }
  }
  
  /** Grow this bit vector to contain at least <code>wd+1</code>
      words. */
  private void grow(int wd) {
    // Assert.check(wd >= this.word.length);
    int newLen = Math.max(this.word.length, wd + 1);
    long[] tmp = new long[newLen];
    System.arraycopy(this.word, 0, tmp, 0, this.word.length);
    this.word = tmp;
  }
    
  /** A <code>BitVector.Iter</code> is an object for enumerating the
      set bits of a given bit vector in order. While the iterator is 
      being used, the bit vector should not be modified.*/
  public static class Iter {
    /*@ non_null */
    long[] word;  // pointer to bit vector's 'word' array
    int wd;       // index of next word to consider
    int bit;      // index of next bit to consider
    long mask;    // mask of next bit to consider
        
    //@ invariant this.wd >= 0
    //@ invariant this.mask == (1L << this.bit)

    /** Construct an empty <code>Iter</code> object. The
	<code>init</code> method must be called before this
	iterator can be used. */
    public Iter() { /*SKIP*/ }
        
    /** Initialize this <code>Iter</code> object for iterating
	over <code>bv</code>. */
    public Iter(BitVector bv) { this.init(bv); }
        
    /** Reinitialize this <code>BVIter</code> object for iterating
	over <code>bv</code>. */
    public void init(BitVector bv) {
      this.word = bv.word;
      this.wd = 0;
      this.bit = 0;
      this.mask = 1L;
    }
        
    /** Return the index of the next set bit in this iterator's
	bit vector, or -1 if there are no more such bits. */
    public int next() {
      for (; this.wd < this.word.length; this.wd++) {
	long w = this.word[this.wd];
	for (; this.bit < 64; this.bit++, this.mask <<= 1) {
	  if ((w & this.mask) != 0L) {
	    int res = (this.wd * 64) + this.bit;
	    // advance to next bit for next call
	    this.bit++;
	    if (this.bit < 64) {
	      this.mask <<= 1;
	    } else {
	      this.wd++;
	      this.bit = 0;
	      this.mask = 1L;
	    }
	    return res;
	  }
	}
	this.bit = 0;
	this.mask = 1L;
      }
      return -1;
    }
  }

}
