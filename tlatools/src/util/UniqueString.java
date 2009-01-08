// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Wed Oct 17 15:25:39 PDT 2001 by yuanyu
package util;

import java.io.*;
import java.util.*;
import tla2sany.semantic.OpDeclNode;

public final class UniqueString implements Serializable {

  /* Maps from strings to variables. */
  public final static InternTable internTbl;

  static {
    internTbl = new InternTable(1024);
  }

  private String s;      // The unique string represented by this.
  private int tok;       // The unique integer assigned to the string.
  private int hashCode;  // The hashCode of this.

  /**
   * If this string is a state variable, this is the location of this
   * variable in a state.  If this string is the name of an operator
   * definition, this is the location of this definition in defns.
   * We assume that there is only one kind of state record active for
   * an entire run.
   */
  private int loc = -1;

  protected UniqueString(String str, int tok) {
    this.s = str;
    this.tok = tok;
    this.hashCode = str.hashCode();
  }

  private UniqueString(String str, int tok, int loc) {
    this(str, tok);
    this.loc = loc;
  }
  
  private static int varCount = 0;

  public static void setVariables(UniqueString[] variables) {
    varCount = variables.length;
    for (int i = 0; i < varCount; i++) {
      variables[i].setLoc(i);
    }
  }
    
  /* Returns the number of variables.  */
  public static int getVarCount() { return varCount; }

  /**
   * Returns the location of this variable in a state, if it is a
   * variable.  Otherwise, returns -1.
   */
  public final int getVarLoc() {
    return (this.loc < varCount) ? this.loc : -1;
  }

  /**
   * Returns the location of this operator in defns, if it is the name
   * of an operator.  Otherwise, returns -1.
   */
  public final int getDefnLoc() {
    return (this.loc < varCount) ? -1 : this.loc;
  }

  // Set this string's location in either the state or the defns.
  public final void setLoc(int loc) { this.loc = loc; }

  public final int getTok() { return this.tok; }

  /**
   * Returns a unique object associated with string str.  That is,
   * the first time uniqueStringOf("foo") is called, it returns a
   * new object o.  Subsequent invocations of uniqueStringOf("foo")
   * return the same object o.
   */
  public static UniqueString uniqueStringOf(String str) {
    return internTbl.put(str);
  }

  /* Same as uniqueStringOf. */
  public static UniqueString intern(String str) {
    return internTbl.put(str);
  }

  public UniqueString concat(UniqueString u) {
    return intern(this.toString() + u.toString());
  }

  /**
   * If there exists a UniqueString object obj such that obj.getTok()
   * equals tok, then uidToUniqueString(i) returns obj; otherwise,    
   * it returns null.
   */
  public static UniqueString uidToUniqueString(int tok) {
    return internTbl.get(tok);
  }
  
  public final String toString() { return this.s; }

  public final int hashCode() { return this.hashCode; }

  public final int length() { return this.s.length(); }
  
  public static void setSource(InternRMI source) {
    internTbl.setSource(source);
  }

  public final int compareTo(UniqueString t) {
    // return this.s.compareTo(t.s);
    return this.tok - t.tok;
  }
  
  public final boolean equals(UniqueString t) { return this.tok == t.tok; }

  // There is no performance gain to compare with a string.
  public final boolean equals(String t) { return this.s.equals(t); }

  public final long fingerPrint(long fp) {
    return FP64.Extend(fp, this.tok);
  }

  public final void write(BufferedDataOutputStream dos) throws IOException {
    dos.writeInt(this.tok);
    dos.writeInt(this.loc);
    dos.writeInt(this.s.length());
    dos.writeString(this.s);
  }

  public static UniqueString read(BufferedDataInputStream dis) throws IOException {
    int tok1 = dis.readInt();
    int loc1 = dis.readInt();
    int slen = dis.readInt();
    String str = dis.readString(slen);
    return new UniqueString(str, tok1, loc1);
  }
  
}
