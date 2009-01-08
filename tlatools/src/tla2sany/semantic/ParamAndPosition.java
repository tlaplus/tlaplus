// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

/** 
 * This class represents a combination of a parameter (OpArgNode) and
 * an argument position for that parameter.  It is wrapped as an
 * object so it can act as a key for Map objects.
 */
class ParamAndPosition {

  SymbolNode param;  
  int        position;

  ParamAndPosition(SymbolNode param, int pos) {
    this.param = param;
    this.position = pos;
  }

  public final int hashCode() {
    return this.param.hashCode() + this.position;
  }

  public final boolean equals(Object obj) {
    if (obj instanceof ParamAndPosition) {
      ParamAndPosition pap = (ParamAndPosition)obj;
      return (this.param == pap.param) && (this.position == pap.position);
    }
    return false;
  }

  public final String toString() {
    return "<" + this.param + ", " + this.position + ">";
  }
  
}
