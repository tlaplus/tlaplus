// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.utilities;

import java.util.Enumeration;
import java.util.Iterator;

final class VectorEnumeration<E> implements Enumeration<E> {
  private final Iterator<E> iterator;

  VectorEnumeration(Iterator<E> iterator) {
    this.iterator = iterator;
  }

  public final boolean hasMoreElements() {
    return iterator.hasNext();
  }

  public final E nextElement() {
    return iterator.next();
  }
}
