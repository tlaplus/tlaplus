// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:03 PST by lamport
//      modified on Fri Feb 16 14:26:21 PST 2001 by yuanyu

package tlc2.util;

import tla2sany.semantic.SymbolNode;

public final class Context {
  /**
   * A link list of name and value pairs.  When adding <name, value> to the context,
   * we assume that name != null.
   */
  
  private SymbolNode name;
  private Object value;
  private Context next;

  public final static Context Empty = new Context(null, null, null);
  
  private Context(SymbolNode name, Object value, Context next) {
    this.name = name;
    this.value = value;
    this.next = next;
  }

  public static Context branch(Context base) {
    return new Context(null, null, base);
  }

  public final Context cons(SymbolNode name, Object value) {
    return new Context(name, value, this);
  }

  /**
   * This method returns the value for the name var. It returns null
   * if this context does not contain var.
   */
  public final Object lookup(SymbolNode var) {
    Context cur;
    for (cur = this; cur.name != null; cur = cur.next) {
      if (var == cur.name) return cur.value;
    }
    if (cur == Empty) return null;
    return cur.next.lookup(var);
  }

  public final Object lookup(SymbolNode var, boolean cutoff) {
    Context cur;
    for (cur = this; cur.name != null; cur = cur.next) {
      if (var == cur.name) return cur.value;
    }
    if (cur == Empty || cutoff) return null;
    return cur.next.lookup(var);
  }

  public final StringBuffer toString(StringBuffer sb) {
    if (this.name == null) {
      if (this == Empty) return sb;
      return this.next.toString(sb);
    }
    sb.append(this.name.getName());
    sb.append("->");
    sb.append(this.value);
    Context cur;
    for (cur = this.next; cur.name != null; cur = cur.next) {
      sb.append(", ");
      sb.append(cur.name.getName());
      sb.append("->");
      sb.append(cur.value);
    }
    cur.toString(sb);
    return sb;
  }
  
  public final String toString() {
    StringBuffer sb = new StringBuffer("[");
    sb = this.toString(sb);
    sb.append("]");
    return sb.toString();
  }
  
}
