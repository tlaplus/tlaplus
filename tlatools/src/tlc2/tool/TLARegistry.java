// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:28 PST by lamport
//      modified on Fri Sep 15 11:06:03 PDT 2000 by yuanyu

package tlc2.tool;

import java.util.*;

public class TLARegistry {

  private static Hashtable javaToTLA = new Hashtable();

  public static String get(String name) {
    return (String)javaToTLA.get(name);
  }

  public static String put(String tname, String jname) {
    return (String)javaToTLA.put(tname, jname);
  }

  public static String mapName(String name) {
    String tname = TLARegistry.get(name);
    return ((tname == null) ? name : tname);
  }

  /* Used only for debugging. */
  public static String allNames() {
    StringBuffer sb = new StringBuffer("{");
    Enumeration eNames = javaToTLA.keys();
    if (eNames.hasMoreElements()) {
      sb.append(eNames.nextElement());
    }
    while (eNames.hasMoreElements()) {
      sb.append(", ");
      sb.append(eNames.nextElement());
    }
    sb.append("}");
    return sb.toString();
  }

}
