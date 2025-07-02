// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import tla2sany.utilities.Vector;

class ParseUnitRelatives {

  final Vector<ParseUnit> extendees  = new Vector<>();

  final Vector<ParseUnit> extendedBy = new Vector<>();

  final Vector<ParseUnit> instancees = new Vector<>();

  final Vector<ParseUnit> instancedBy = new Vector<>();

  public final String toString() {
    return "[ extendees = "   + extendees.toString() +
           ", extendedBy = "  + extendedBy.toString() +
           ", instancees = "  + instancees.toString() +
           ", instancedBy = " + instancedBy.toString() +
           " ]";
  }

}
