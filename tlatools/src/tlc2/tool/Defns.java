// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:55 PST by lamport
//      modified on Sat Jun 30 10:05:29 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.*;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.OpDefNode;
import util.UniqueString;
import tlc2.util.*;

public class Defns implements ToolGlobals, Serializable {
  /**
   * There are two kinds of definitions stored in the table:
   * an OpDefNode or a TLC value. A java override method is
   * stored as a MethodValue.
   */
  private static int defnIdx;
  
  private Object[] table;

  public Defns() { this.table = new Object[defnIdx+32]; }

  public static void init() {
    defnIdx = UniqueString.getVarCount();
  }

  /**
   * Returns the definition of key if its definition exists.
   * Otherwise, returns null.
   */
  public final Object get(UniqueString key) {
    int loc = key.getDefnLoc();
    if (loc < 0 || loc >= this.table.length) {
      return null;
    }
    return this.table[loc];
  }

  public final Object get(String key) {
    UniqueString var = UniqueString.intern(key);
    return this.get(var);
  }

  /**
   * Store a new definition for key.  If there was an entry in the
   * table for the key, overwrite it.
   */
  public final void put(UniqueString key, Object val) {
    int loc = key.getDefnLoc();
    if (loc == -1) {
      loc = defnIdx++;
      key.setLoc(loc);
    }
    if (loc >= this.table.length) {
      int oldSize = this.table.length;
      int newSize = Math.max(2*oldSize, loc+1);
      Object[] old = this.table;
      this.table = new Object[newSize];
      for (int i = 0; i < oldSize; i++) {
	this.table[i] = old[i];
      }
    }
    this.table[loc] = val;
  }

  public final void put(String key, Object val) {
    this.put(UniqueString.intern(key), val);
  }

}
