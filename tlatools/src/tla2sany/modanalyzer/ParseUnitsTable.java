// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import java.util.Enumeration;
import java.util.Hashtable;

/**
 * Each instance of this class basically is a map from ParseUnit objects to
 * ParseUnitRelatives objects.
 *
 * It is just a wrapper for a Hashtable, with the added benefit of type checking
 */

class ParseUnitsTable {

  // Maps ParseUnit string names to their respective ParseUnit objects
  Hashtable parseUnitTable = new Hashtable();

  ParseUnit get(String parseUnitName) { 
    return (ParseUnit)parseUnitTable.get(parseUnitName); 
  }

  void put (ParseUnit parseUnitName, ParseUnit parseUnit) {
    parseUnitTable.put(parseUnitName, parseUnit);
  }

  Enumeration getKeys() { return parseUnitTable.keys(); }  

  public String toString() {
    String ret = "";

    Enumeration e = parseUnitTable.keys();
    while ( e.hasMoreElements()) {
      ret += "[ ParseUnit: " + ((ParseUnit)e.nextElement()).getName() + " ] ";
    }
    return ret;
  }

}
