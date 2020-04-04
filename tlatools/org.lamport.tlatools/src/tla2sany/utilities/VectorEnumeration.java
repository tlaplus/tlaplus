// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.utilities;
import java.util.Enumeration;

final class VectorEnumeration<E> implements Enumeration<E> {
  int index = 0;
  Object data[];

  VectorEnumeration( Object info[], int size ) {
    data = new Object[ size ];
    System.arraycopy( info, 0, data, 0, size );
  }

  public final boolean hasMoreElements() {
    return index < data.length;
  }

  @SuppressWarnings("unchecked")
  public final E nextElement() {
    if (index < data.length)
      return (E)data[index++];
    else
      throw new java.util.NoSuchElementException();
  }
}
