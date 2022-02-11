// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

class SetOfLevelConstraints extends HashMap<SymbolNode, Integer> implements LevelConstants {
  // Implements a map mapping parameters to levels. An entry <p,x> in
  // the set means that p must have a level <= x.
  /*************************************************************************
  * In other words, this is a HashMap of elements whose key is a           *
  * SymbolNode and whose value is an int.  An entry in this table means    *
  * that the key/parameter must have a level <= the value/int.             *
  *************************************************************************/
  
  /**
   * This method adds <param, level> into this map. It subsumes
   * any existing one. 
   */
  @Override
  public final Integer put(SymbolNode param, Integer level) {
    int newLevel = level.intValue();
    Integer old = this.get(param);

    int oldLevel = (old == null) ? MaxLevel : old.intValue();
    super.put(param, new Integer(Math.min(newLevel, oldLevel)));
    return old;
  }
  
  /**
   * This method adds all of the elements of its argument "s" to this
   * map, in each case "subsuming" it with any constraint already
   * present for the same parameter if one is there.
   */
  @Override
  public final void putAll(Map<? extends SymbolNode, ? extends Integer> s) {
    for (Iterator<? extends SymbolNode> iter = s.keySet().iterator(); iter.hasNext(); ) {
      SymbolNode key = iter.next();
      this.put(key, s.get(key));
    }
  }
  
  @Override
  public final String toString() {
    StringBuffer sb = new StringBuffer("{ ");
    for (Iterator<SymbolNode> iter = this.keySet().iterator(); iter.hasNext(); ) {
      SymbolNode param = iter.next();
      sb.append(param.getName() + " -> " + this.get(param));
      if (iter.hasNext()) sb.append(", ");
    }
    sb.append("}");
    return sb.toString();
  }
}
