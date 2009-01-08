// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:34 PST by lamport
//      modified on Sun Aug 26 20:11:53 PDT 2001 by yuanyu

package tlc2.util;

public final class ObjLongTable {
  private int count;
  private int length;
  private int thresh;
  private Object[] keys;
  private long[] elems;

  public ObjLongTable(int size) {
    this.keys = new Object[size];
    this.elems = new long[size];
    this.count = 0;
    this.length = size;
    this.thresh = this.length / 2;
  }

  private final void grow() {
    Object[] oldKeys = this.keys;
    long[] oldElems = this.elems;
    this.count = 0;
    this.length = 2 * this.length + 1;
    this.thresh = this.length / 2;
    this.keys = new Object[this.length];
    this.elems = new long[this.length];
    for (int i = 0; i < oldKeys.length; i++) {
      Object key = oldKeys[i];
      if (key != null) this.put(key, oldElems[i]);
    }
  }

  public final int size() { return this.count; }

  public final int put(Object k, long elem) {
    if (count >= thresh) this.grow();
    int loc = ((int)k.hashCode() & 0x7FFFFFFF) % this.length;
    while (true) {
      Object key = this.keys[loc];
      if (key == null) {
	this.keys[loc] = k;
	this.elems[loc] = elem;
	this.count++;
	return loc;
      }
      else if (key.equals(k)) {
	this.elems[loc] = elem;
	return loc;
      }
      loc = (loc + 1) % this.length;
    }
  }

  public final int add(Object k, long elem) {
    if (count >= thresh) this.grow();
    int loc = ((int)k.hashCode() & 0x7FFFFFFF) % this.length;
    while (true) {
      Object key = this.keys[loc];
      if (key == null) {
	this.keys[loc] = k;
	this.elems[loc] = elem;
	this.count++;
	return loc;
      }
      else if (key.equals(k)) {
	this.elems[loc] += elem;
	return loc;
      }
      loc = (loc + 1) % this.length;
    }
  }
  
  public final long get(Object k) {
    int loc = ((int)k.hashCode() & 0x7FFFFFFF) % length;
    while (true) {
      Object key = this.keys[loc];
      if (key == null) return 0;
      if (key.equals(k)) return this.elems[loc];
      loc = (loc + 1) % length;
    }
  }

  public final String[] sortStringKeys() {
    String[] res = new String[this.count];
    int idx = -1;
    for (int i = 0; i < this.length; i++) {
      String key = (String)this.keys[i];
      if (key != null) {
	int j = idx;
	while (j >= 0) {
	  if (res[j].compareTo(key) <= 0) break;
	  res[j+1] = res[j];
	  j--;
	}
	res[j+1] = key;
	idx++;
      }
    }
    return res;
  }
  

  public final Enumerator keys() { return new Enumerator(); }

  public final class Enumerator {
    int index = 0;

    public final Object nextElement() {
      while (this.index < keys.length) {
	if (keys[this.index] != null) {
	  return keys[this.index++];
	}
	this.index++;
      }
      return null;
    }
  }
    

}
