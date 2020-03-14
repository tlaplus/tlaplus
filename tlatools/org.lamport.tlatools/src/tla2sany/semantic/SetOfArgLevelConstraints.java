// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

class SetOfArgLevelConstraints extends HashMap<ParamAndPosition, Integer> implements LevelConstants {
  // Implements a map mapping arg-level parameters (ParamAndPosition)
  // to levels (Integer). An entry <pap,x> means that the argument
  // pap.position of the operator pap.param must have a level >= x.
  /*************************************************************************
  * An element in this HashMap has key that is a ParamAndPosition and      *
  * value that is an int.  Such an element with key k and value v means    *
  * that the operator parameter described by the SymbolNode k.param must   *
  * be able to accept an argument of level v in its argument number        *
  * k.position.                                                            *
  *************************************************************************/
  
  /**
   * This method adds <pap, level> into this set, and "subsumes"
   * it with another one for the same parameter if one is there, or
   * ignoring the constraint if it is vacuous.
   */
  @Override
  public final Integer put(ParamAndPosition pap, Integer level) {
    int newLevel = level.intValue();
    Integer old = this.get(pap);

    int oldLevel = (old == null) ? MinLevel : old.intValue();
    super.put(pap, new Integer(Math.max(newLevel, oldLevel)));
    return old;
  }

  public final Integer put(SymbolNode param, int position, int level) {
    ParamAndPosition pap = new ParamAndPosition(param, position);
    return this.put(pap, new Integer(level));
  }

  /**
   * This method adds all of the elements of its argument s to this
   * map, in each case "subsuming" it with any constraint already
   * present for the same parameter if one is there.
   */
  @Override
  public final void putAll(Map<? extends ParamAndPosition, ? extends Integer> s) {
    for (Iterator<? extends ParamAndPosition> iter = s.keySet().iterator(); iter.hasNext(); ) {
    	  ParamAndPosition key = iter.next();
      this.put(key, s.get(key));
    }
  }

  @Override
  public final String toString() {
    StringBuffer sb = new StringBuffer("{ ");
    for (Iterator<ParamAndPosition> iter = this.keySet().iterator(); iter.hasNext(); ) {
      ParamAndPosition pap = iter.next();
      sb.append(pap.toString() + " -> " + this.get(pap));
      if (iter.hasNext()) sb.append(", ");
    }
    sb.append("}");
    return sb.toString();
  }

}
