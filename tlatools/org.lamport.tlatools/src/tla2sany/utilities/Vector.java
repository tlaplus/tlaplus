// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.utilities;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Iterator;

/**
 * Legacy wrapper around {@link ArrayList} to preserve historical semantics:
 * <ul>
 *   <li>{@link #contains(Object)} uses reference equality (==), not {@link Object#equals(Object)}.</li>
 *   <li>{@link #insertElementAt(Object, int)} rejects {@code index == size()} (cannot append via insert).</li>
 *   <li>{@link #elements()} returns a snapshot Enumeration taken at call time.</li>
 * </ul>
 * These differences make a drop-in replacement with {@link ArrayList} unsafe until all call sites
 * are audited for identity-based membership checks.
 */
public class Vector<E> extends ArrayList<E> {
  static int defaultSize = 10;

  public Vector() {
    super(defaultSize);
  }

  public Vector(int initialSize) {
    super(initialSize);
  }

  public final void addElement(E obj) {
    super.add(obj);
  }

  public final E firstElement() {
    return elementAt(0);
  }

  public final E lastElement() {
    return elementAt(size() - 1);
  }

  public final E elementAt(int i) {
    checkBounds(i);
    return super.get(i);
  }

  public final void removeAllElements() {
    super.clear();
  }

  public final void removeElementAt(int i) {
    checkBounds(i);
    super.remove(i);
  }

  public final void insertElementAt(E obj, int i) {
    // The legacy implementation forbids inserting at the end (i == size()).
    if (i < 0 || i >= size()) {
      throw new ArrayIndexOutOfBoundsException();
    }
    super.add(i, obj);
  }

  public final void setElementAt(E obj, int i) {
    checkBounds(i);
    super.set(i, obj);
  }

  @Override
  public final boolean contains(Object obj) {
    for (E value : this) {
      if (value == obj) {
        return true;
      }
    }
    return false;
  }

  public final Enumeration<E> elements() {
    // Return a snapshot to preserve the legacy behavior where enumeration
    // reflects the elements present at creation time.
    return new VectorEnumeration<E>(new ArrayList<E>(this).iterator());
  }

  public final void append(Vector<E> v) {
    super.addAll(v);
  }

  // Like the append method above, but elements of v will not be added to THIS Vector
  // if they are already present at least once; repeated elements already in
  // THIS Vector, however, will not be removed.
  public final void appendNoRepeats(Vector<E> v) {
    for (int i = 0; i < v.size(); i++) {
      if (!this.contains(v.elementAt(i))) {
        this.addElement(v.elementAt(i));
      }
    }
  }

  @Override
  public final String toString() {
    String ret;
    ret = "[ ";
    if (this.size() > 0) ret += this.elementAt(0).toString();
    for (int i = 1; i<this.size(); i++) {
      ret += ", " + this.elementAt(i).toString();
    }
    return ret + " ]";
  } // end toString()

  private void checkBounds(int i) {
    if (i < 0 || i >= size()) {
      throw new ArrayIndexOutOfBoundsException();
    }
  }
}
