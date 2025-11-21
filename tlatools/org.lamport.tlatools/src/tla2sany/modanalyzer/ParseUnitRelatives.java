// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import java.util.ArrayList;

class ParseUnitRelatives {

  final ArrayList<ParseUnit> extendees  = new ArrayList<>();

  final ArrayList<ParseUnit> extendedBy = new ArrayList<>();

  final ArrayList<ParseUnit> instancees = new ArrayList<>();

  final ArrayList<ParseUnit> instancedBy = new ArrayList<>();

  public final String toString() {
    return "[ extendees = "   + extendees.toString() +
           ", extendedBy = "  + extendedBy.toString() +
           ", instancees = "  + instancees.toString() +
           ", instancedBy = " + instancedBy.toString() +
           " ]";
  }

}
