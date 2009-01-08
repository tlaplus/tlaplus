// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.utilities;
import java.util.Enumeration;

public class Vector {
  static int defaultSize = 10;
  
  protected Object info[];
  protected int size = 0;
  protected int capacity;
  protected int increment;

  public Vector() {
    info = new Object[ defaultSize ];
    capacity = defaultSize;
    increment = defaultSize;
  }

  public Vector(int initialSize ) {
    info = new Object[ initialSize ];
    capacity = initialSize;
    increment = initialSize;
  }

  public final int size() {
    return size;
  }

  /* Method replaced below
  public final String toString() {
    String ret="";

    for (int i = 0; i < size; i++) {
      ret = ret + info[i].toString();
    }

    return ret;
  }
  */

  public final void addElement( Object obj ) {
    if (size == capacity) {
      Object next[] = new Object[ capacity + increment ];
      System.arraycopy( info, 0, next, 0, capacity );
      capacity+= increment;
      info = next;
    }
    info[ size ] = obj;
    size++;
  }

  public final Object firstElement() {
    return info[0];
  }

  public final Object lastElement() {
    return info[ size-1 ];
  }

  public final Object elementAt(int i) {
    if (i < 0 || i >= size )
      throw new ArrayIndexOutOfBoundsException();
    else
      return info[ i ];
  }

  public final void removeAllElements() {
    for (int lvi = 0; lvi < size; lvi++ ) {
      info[lvi] = null;
    }
    size = 0;
  }

  public final void removeElementAt( int i ) {
    if (i < 0 || i >= size )
      throw new ArrayIndexOutOfBoundsException();
    else {
      for (int lvi = i+1; lvi < size; lvi++ )
        info[ lvi-1 ] = info [lvi];
      size--;
      info[ size ] = null;
    }
  }

  public final void insertElementAt( Object obj, int i ) {
    if (i < 0 || i >= size )
      throw new ArrayIndexOutOfBoundsException();
    else if (size == capacity) {
      Object next[] = new Object[ capacity + increment ];
      System.arraycopy( info, 0, next, 0, i );
      next[i] = obj;
      System.arraycopy( info, i, next, i+1, capacity - i );
      capacity+= increment;
      info = next;
    } else {
      for ( int lvi = size; lvi > i; lvi-- )
        info[ lvi ] = info[lvi-1];
      info[ i ] = obj;
    }
    size++;
  }

  public final void setElementAt( Object obj, int i ) {
    if (i < 0 || i >= size )
      throw new ArrayIndexOutOfBoundsException();
    else 
      info[ i ] = obj;
  }

  public final boolean contains (Object obj) {
    for (int i = 0; i < size; i++) {
      if ( info[ i ] == obj ) return true;
    }
    return false; 
  }

  public final Enumeration elements() {
    return new VectorEnumeration( info, size );
  }

  public final void append( Vector v ) {
    if ( v.size + size  > capacity ) {
      Object neo[] = new Object[ capacity + v.capacity ];
      capacity += v.capacity;
      System.arraycopy( info, 0, neo, 0, size );
      info = neo;
    }
    System.arraycopy( v.info, 0, info, size, v.size );
    size += v.size;
  }

  // Like the append method above, but elements of v will not be added to THIS Vector 
  // if they are already present at least once; repeated elements already in 
  // THIS Vector, however, will not be removed.
  public final void appendNoRepeats(Vector v) {
    for (int i = 0; i < v.size(); i++) {
      if ( ! this.contains(v.elementAt(i)) ) this.addElement(v.elementAt(i));
    }
  }

  public final String toString() {
    String ret;
    ret = "[ ";
    if (this.size() > 0) ret += this.elementAt(0).toString();
    for (int i = 1; i<this.size(); i++) {
      ret += ", " + this.elementAt(i).toString();
    }
    return ret + " ]";
  } // end toString()
}
