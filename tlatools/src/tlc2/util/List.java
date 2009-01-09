// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:30 PST by lamport
//      modified on Mon Sep 25 13:25:21 PDT 2000 by yuanyu

package tlc2.util;


public class List {
  public class ConsCell {
    protected Object value;
    protected ConsCell next;

    ConsCell(Object value, ConsCell next) {
      this.value = value;
      this.next = next;
    }
  }
  
  public static List Empty = new List();
  protected ConsCell first;
  protected ConsCell last;

  /* Constructors.  */
  public List() { this.first = null; this.last = null; }

  public List(Object value) {
    this.first = new ConsCell(value, null);
    this.last = this.first;
  }

  public List(List lst) {
    this.first = lst.first;
    this.last = lst.last;
  }

  /* This method returns true iff the list is empty. */
  public final boolean isEmpty() { return (this.first == null); }

  /* This method returns the length of the list.  */
  public final int length() {
    int len = 0;
    ConsCell work = this.first;
    while (work != null) {
      len++;
      work = work.next;
    }
    return len;
  }

  /**
   * This method adds (destructively) a new element in the front 
   * of the list.
   */
  public final void push(Object value) {
    ConsCell cell = new ConsCell(value, this.first);
    this.first = cell;
    if (this.last == null) this.last = cell;
  }

  /**
   * This method removes (destructively) one element from the
   * front of the list.  It returns the removed element.
   */
  public final Object pop() {
    // Assert.check(this.first != null);
    Object result = this.first.value;
    this.first = this.first.next;
    if (this.first == null) this.last = null;
    return result;
  }

  /**
   * This method is the cons equivalent. It returns a new list
   * of adding a new element in the front.
   */
  public final List cons(Object value) {
    ConsCell cell = new ConsCell(value, this.first);
    List newList = new List();
    newList.first = cell;
    newList.last = (this.last == null) ? cell : this.last;
    return newList;
  }

  /**
   * This method is the car equivalent. It returns the first
   * element of the list.
   */
  public final Object car() {
    // Assert.check(this.first != null);
    return this.first.value;
  }

  /**
   * This method is the cdr equivalent. It returns a new list
   * of removing the first front element.
   */
  public final List cdr() {
    // Assert.check(this.first != null);
    List newList = new List();
    newList.first = this.first.next;
    newList.last = (newList.first == null) ? null : this.last;
    return newList;
  }

  /**
   * This method returns true iff the argument is a member of
   * the list. The equality check is on reference.
   */
  public final boolean member(Object value) {
    ConsCell cell = this.first;
    boolean isMember = false;
    while (cell != null) {
      if (cell.value == value) {
	isMember = true;
	break;
      }
      cell = cell.next;
    }
    return isMember;
  }

  /**
   * This method returns a new list that appends one element
   * at the end of this list.
   */
  public final List append1(Object value) {
    ConsCell cell = this.first;
    if (cell == null) return new List(value);

    List newList = new List(cell.value);
    cell = cell.next;
    while (cell != null) {
      ConsCell newCell = new ConsCell(cell.value, null);
      newList.last.next = newCell;
      newList.last = newCell;
      cell = cell.next;
    }
    ConsCell newCell = new ConsCell(value, null);
    newList.last.next = newCell;
    newList.last = newCell;
    return newList;
  }

  /* This method returns a new list that appends two lists. */
  public final List append(List lst) {
    ConsCell cell = this.first;
    if (cell == null) return new List(lst);

    List newList = new List(cell.value);
    cell = cell.next;
    while (cell != null) {
      ConsCell newCell = new ConsCell(cell.value, null);
      newList.last.next = newCell;
      newList.last = newCell;
      cell = cell.next;
    }
    cell = lst.first;
    while (cell != null) {
      ConsCell newCell = new ConsCell(cell.value, null);
      newList.last.next = newCell;
      newList.last = newCell;
      cell = cell.next;      
    }
    return newList;
  }

  /**
   * This method appends (destructively) an element to the end
   * of this list.
   */
  public final List append1D(Object value) {
    if (this.first == null) {
      this.first = new ConsCell(value, null);
      this.last = this.first;
    }
    else {
      this.last.next = new ConsCell(value, null);
      this.last = this.last.next;
    }
    return this;
  }

  /**
   * This method appends (destructively) a list to the end
   * of this list.
   */
  public final List appendD(List lst) {
    if (this.first == null) {
      this.first = lst.first;
    }
    else {
      this.last.next = lst.first;
    }
    if (lst.first != null) {
      this.last = lst.last;
    }
    return this;
  }

  /* The string representation. */
  public final String toString() {
    StringBuffer sb = new StringBuffer("[");
    ConsCell work = this.first;
    while (work != null) {
      sb.append(work.value.toString());
      work = work.next;
    }
    sb.append("]");
    return sb.toString();
  }

}
