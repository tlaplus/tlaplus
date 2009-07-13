// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Tue Sep 12 14:46:23 PDT 2000 by yuanyu  
//      modified on Thu Jul  9 22:10:25 PDT 1998 by manolios

/**
 * This class was derived from the HashTable implementation
 * in Sun's JDK. It supports quick membership check.
 */
package util;

import java.io.IOException;
import java.util.Enumeration;
import java.util.NoSuchElementException;

class SetEntry {
  /*
   * Set collision list.
   */
  int hash;
  Object key;
  SetEntry next;

  protected Object clone() {
    SetEntry entry = new SetEntry();
    entry.hash = hash;
    entry.key = key;
    entry.next = (next != null) ? (SetEntry)next.clone() : null;
    return entry;
  }
}

/**
 * This class implements a set. Any non-<code>null</code> object can
 * be used as a key (element).
 * <p>
 * To successfully store and retrieve objects from a set, the element
 * objects used as keys must implement the <code>hashCode</code> 
 * method and the <code>equals</code> method. 
 * <p>
 * An instance of <code>Set</code> has two parameters that affect its
 * efficiency: its <i>capacity</i> and its <i>load factor</i>. The 
 * load factor should be between 0.0 and 1.0. When the number of entries
 * in the set exceeds the product of the load factor and the current
 * capacity, the capacity is increased by calling the <code>rehash</code>
 * method. Larger load factors use memory more efficiently, at the 
 * expense of larger expected time per lookup. 
 * <p>
 * If many entries are to be made into a <code>Set</code>, creating it
 * with a sufficiently large capacity may allow the entries to be 
 * inserted more efficiently than letting it perform automatic rehashing
 * as needed to grow the set.
 * <p>
 * </pre></blockquote>
 */
public class Set implements Cloneable, java.io.Serializable {
    /*
     * A set of objects.
     */
    private transient SetEntry set[];

    /* The total number of elements in the set.  */
    private transient int count;

    /* Rehashes the set when count exceeds this threshold.  */
    private int threshold;

    /* The load factor for the set.    */
    private float loadFactor;

    /* use serialVersionUID from JDK 1.0.2 for interoperability */
    private static final long serialVersionUID = 1421746759512286392L;

    /*
     * Constructs a new, empty set with the specified initial 
     * capacity and the specified load factor. 
     *
     * @param      initialCapacity   the initial capacity of the set.
     * @param      loadFactor        a number between 0.0 and 1.0.
     * @exception  IllegalArgumentException  if the initial capacity is less
     *               than or equal to zero, or if the load factor is less than
     *               or equal to zero.
     * @since      JDK1.0
     */
    public Set(int initialCapacity, float loadFactor) {
      if ((initialCapacity <= 0) || (loadFactor <= 0.0)) {
	throw new IllegalArgumentException();
      }
      this.loadFactor = loadFactor;
      set = new SetEntry[initialCapacity];
      threshold = (int)(initialCapacity * loadFactor);
    }

    /*
     * Constructs a new empty set with the specified initial capacity
     * and default load factor.
     *
     * @param   initialCapacity   the initial capacity of the set.
     */
    public Set(int initialCapacity) {
      this(initialCapacity, 0.75f);
    }

    /*
     * Constructs a new, empty set with a default capacity and load
     * factor. 
     */
    public Set() { this(101, 0.75f); }

    /*
     * Returns the number of keys in this set.
     *
     * @return  the number of keys in this set.
     */
    public int size() { return this.count; }

    /*
     * Tests if this set is empty.
     *
     * @return  <code>true</code> if this set is empty.
     *          <code>false</code> otherwise.
     * @since   JDK1.0
     */
    public boolean isEmpty() { return count == 0; }

    /*
     * Returns an enumeration of the elements in this set.
     *
     * @return  an enumeration of the elements in this set.
     * @see     java.util.Enumeration
     */
    public synchronized Enumeration elements() {
      return new SetEnumerator(set);
    }

    /*
     * Tests if the specified object is an element in this set.
     * 
     * @param   key   possible key.
     * @return  <code>true</code> if the specified object is an element
     *          in this set; <code>false</code> otherwise.
     */
    public synchronized boolean contains(Object key) {
      SetEntry tab[] = set;
      int hash = key.hashCode();
      int index = (hash & 0x7FFFFFFF) % tab.length;
      for (SetEntry e = tab[index] ; e != null ; e = e.next) {
	if ((e.hash == hash) && e.key.equals(key)) {
	  return true;
	}
      }
      return false;
    }

    /*
     * Rehashes the contents of the set into a set with a larger capacity.
     * This method is called automatically when the number of keys in the
     * set exceeds this set's capacity and load factor. 
     */
    protected void rehash() {
      int oldCapacity = set.length;
      SetEntry oldSet[] = set;
	
      int newCapacity = oldCapacity * 2 + 1;
      SetEntry newSet[] = new SetEntry[newCapacity];

      threshold = (int)(newCapacity * loadFactor);
      set = newSet;

      for (int i = oldCapacity ; i-- > 0 ;) {
	for (SetEntry old = oldSet[i] ; old != null ; ) {
	  SetEntry e = old;
	  old = old.next;

	  int index = (e.hash & 0x7FFFFFFF) % newCapacity;
	  e.next = newSet[index];
	  newSet[index] = e;
	}
      }
    }

    /*
     * Puts the specified <code>key</code> as an element into this set.
     * The key can not be <code>null</code>. 
     * <p>
     * @param      key     the element.
     * @return     the previous copy of the element in this set,
     *             or <code>null</code> if it did not have one.
     * @exception  NullPointerException  if the element is <code>null</code>.
     * @see     java.lang.Object#equals(java.lang.Object)
     */
    public synchronized Object put(Object key) {
      // Makes sure the key is not already in the set.
      SetEntry tab[] = set;
      int hash = key.hashCode();
      int index = (hash & 0x7FFFFFFF) % tab.length;
      for (SetEntry e = tab[index] ; e != null ; e = e.next) {
	if ((e.hash == hash) && e.key.equals(key)) {
	  Object old = e.key;
	  e.key = key;
	  return old;
	}
      }
      
      if (count >= threshold) {
	// Rehash the set if the threshold is exceeded
	rehash();
	return put(key);
      } 

      // Creates the new entry.
      SetEntry e = new SetEntry();
      e.hash = hash;
      e.key = key;
      e.next = tab[index];
      tab[index] = e;
      count++;
      return null;
    }

    /*
     * Removes the key (element) from this set. This method does nothing
     * if the key is not in the set.
     *
     * @param   key   the key that needs to be removed.
     * @return  the element in this set, or <code>null</code> if the key
     *          is not in the set.
     */
    public synchronized Object remove(Object key) {
      SetEntry tab[] = set;
      int hash = key.hashCode();
      int index = (hash & 0x7FFFFFFF) % tab.length;
      for (SetEntry e = tab[index], prev = null ; e != null ; prev = e, e = e.next) {
	if ((e.hash == hash) && e.key.equals(key)) {
	  if (prev != null) {
	    prev.next = e.next;
	  } else {
	    tab[index] = e.next;
	  }
	  count--;
	  return e.key;
	}
      }
      return null;
    }

    /*
     * Empty this set.
     */
    public synchronized void clear() {
      SetEntry tab[] = set;
      for (int index = tab.length; --index >= 0; )
	tab[index] = null;
      count = 0;
    }

    /*
     * Creates a shallow copy of this set. The elements themselves are
     * not cloned. 
     * This is a relatively expensive operation.
     *
     * @return  a clone of the set.
     */
    public synchronized Object clone() {
      try { 
	Set t = (Set)super.clone();
	t.set = new SetEntry[set.length];
	for (int i = set.length ; i-- > 0 ; ) {
	  t.set[i] = (set[i] != null) ? (SetEntry)set[i].clone() : null;
	}
	return t;
      } catch (CloneNotSupportedException e) { 
	// this shouldn't happen, since we are Cloneable
	throw new InternalError();
      }
    }

    /*
     * Returns a rather long string representation of this set.
     *
     * @return a string representation of this set.
     */
    public synchronized String toString() {
	int max = size() - 1;
	StringBuffer buf = new StringBuffer();
	Enumeration e = elements();
	buf.append("{");

	for (int i = 0; i <= max; i++) {
	    String s1 = e.nextElement().toString();
	    buf.append(s1);
	    if (i < max) buf.append(", ");
	}
	buf.append("}");
	return buf.toString();
    }

    /*
     * WriteObject is called to save the state of the set to a stream.
     * Only the elements are serialized since the hash values may be
     * different when the contents are restored.
     * iterate over the contents and write out the elements.
     */
    private synchronized void writeObject(java.io.ObjectOutputStream s)
    throws IOException {
      // Write out the length, threshold, loadfactor
      s.defaultWriteObject();

      // Write out length, count of elements and then the key/value objects
      s.writeInt(set.length);
      s.writeInt(count);
      for (int index = set.length-1; index >= 0; index--) {
	SetEntry entry = set[index];

	while (entry != null) {
	  s.writeObject(entry.key);
	  entry = entry.next;
	}
      }
    }

    /*
     * readObject is called to restore the state of the set from
     * a stream.  Only the elements are serialized since the
     * hash values may be different when the contents are restored.
     * Read count elements and insert into the set.
     */
    private synchronized void readObject(java.io.ObjectInputStream s)
    throws IOException, ClassNotFoundException {
	// Read in the length, threshold, and loadfactor
	s.defaultReadObject();

	// Read the original length of the array and number of elements
	int origlength = s.readInt();
	int elements = s.readInt();

	// Compute new size with a bit of room 5% to grow but
	// No larger than the original size.  Make the length
	// odd if it's large enough, this helps distribute the entries.
	// Guard against the length ending up zero, that's not valid.
	int length = (int)(elements * loadFactor) + (elements / 20) + 3;
	if (length > elements && (length & 1) == 0) length--;
	if (origlength > 0 && length > origlength) length = origlength;

	set = new SetEntry[length];
	count = 0;

	// Read the number of elements and then all the key/value objects
	for (; elements > 0; elements--) {
	    Object key = s.readObject();
	    put(key);
	}
    }

  /**
   * Checks for set containment, ie. is x in this? It is just another
   * way to write the hashtable containsKey.
   */
  public synchronized boolean in(Object x) {
    return contains(x);
  }

  /**
   * Destructively modify this so that it becomes the intersection of
   * itself with x.  We iterate over the elements in this and remove any
   * that are not also in x.
   */
  public void intersection (Set x) { 
    Enumeration elements = elements();
    Object a;
    while (elements.hasMoreElements()) {
      a = elements.nextElement();
      if (! x.in(a))
	remove(a);
    }
  }

  /**
   * Create a new set which is the intersection of x and y.  We clone
   * the smaller (set size) of x, y because that's what intersection
   * iterates on.
   */
  public static Set intersection(Set x, Set y) {
    Set result = new Set();
    if (x.size() < y.size()) {
      result = (Set) x.clone();
      result.intersection(y);
    }
    else {
      result = (Set) x.clone();
      result.intersection(y);
    }
    return result;
  }

  /**
   * Destructively modify this so that it becomes the union of itself
   * with x.  We iterate over the elements in x, adding to this any that
   * are not in x.
   */
  public void union(Set x) { 
    Enumeration elements = x.elements();
    while (elements.hasMoreElements()) 
      put(elements.nextElement());
  }

  /**
   * Create a new set which is the union of x and y.  We clone the
   * larger (set size) of x, y because union iterates on the one not
   * cloned.
   */
  public static Set union(Set x, Set y) {
    Set result = new Set();
    if (x.size() > y.size()) {
      result = (Set) x.clone();
      result.union(y);
    }
    else {
      result = (Set) x.clone();
      result.union(y);
    }
    return result;
  }

  /**
   * Destructively modify this so that all elements in x are removed.
   * If |this| > |x| we iterate over the elements in x, removing them all
   * from this.  Otherwise, we iterate over the elements in this, removing
   * any that are in x.
   */
  public void minus(Set x) { 
    if (size() > x.size()) {
      Enumeration elements = x.elements();
      while (elements.hasMoreElements()) 
	remove(elements.nextElement());
    }
    else {
      Enumeration elements = elements();
      Object a;
      while (elements.hasMoreElements()) {
	a = elements.nextElement();
	if (x.in(a))
	  remove(a);
      }
    }
  }

  /* Create a new set which equals x - y.  */
  public static Set minus(Set x, Set y) {
    Set result = (Set) x.clone();
    result.minus(y);
    return result;
  }

  /* Complementation with respect to universe u. */
  public static Set complement (Set x, Set u) { return minus(u, x); }

  /* Is this a subset of x. */  
  public boolean subset (Set x) {
    Enumeration elements = elements();
    while (elements.hasMoreElements()) 
      if (! x.in(elements.nextElement()))
	return false;
    return true;
  }
 
  /* Is x a subset of y?  */
  public static boolean subset (Set x, Set y) { return x.subset(y); }

  /* Is this equal (as a set) to x?   */
  public boolean equal (Set x) {
    return (subset(x) && x.subset(this));
  }
 
  /* Is x equal (as a set) to y? */
  public static boolean equal (Set x, Set y) { return x.equal(y); }
}

/*
 * A set enumerator class.  This class should remain opaque 
 * to the client. It will use the Enumeration interface. 
 */
class SetEnumerator implements Enumeration {
  int index;
  SetEntry set[];
  SetEntry entry;

  SetEnumerator(SetEntry set[]) {
    this.set = set;
    this.index = set.length;
  }
	
  public boolean hasMoreElements() {
    if (entry != null) {
      return true;
    }
    while (index-- > 0) {
      if ((entry = set[index]) != null) {
	return true;
      }
    }
    return false;
  }

  public Object nextElement() {
    if (entry == null) {
      while ((index-- > 0) && ((entry = set[index]) == null));
    }
    if (entry != null) {
      SetEntry e = entry;
      entry = e.next;
      return e.key;
    }
    throw new NoSuchElementException("SetEnumerator");
  }
}
