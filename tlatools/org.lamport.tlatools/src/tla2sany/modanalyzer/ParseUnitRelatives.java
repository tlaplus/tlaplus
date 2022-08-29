// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import java.util.ArrayList;

class ParseUnitRelatives {

    final ArrayList<ParseUnit> extendees = new ArrayList<>();  // ArrayList of ParseUnit objects

    final ArrayList<ParseUnit> extendedBy = new ArrayList<>();  // ArrayList of ParseUnit objects

    final ArrayList<ParseUnit> instancees = new ArrayList<>();  // ArrayList of ParseUnit objects

    final ArrayList<ParseUnit> instancedBy = new ArrayList<>();  // ArrayList of ParseUnit objects

    public final String toString() {
        return "[ extendees = " + extendees +
                ", extendedBy = " + extendedBy +
                ", instancees = " + instancees +
                ", instancedBy = " + instancedBy +
                " ]";
    }

}
