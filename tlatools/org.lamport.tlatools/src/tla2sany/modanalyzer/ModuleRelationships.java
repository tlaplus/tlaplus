// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import java.util.Enumeration;
import java.util.Hashtable;

/**
 * Each instance of this class basically is a map from ModulePointer objects to
 * ModuleRelatives objects.
 * <p>
 * It is primarily a wrapper for a Hashtable, with the added benefit of type checking
 */

class ModuleRelationships {

    // Maps ModulePointer objects to ModuleRelatives objects
    private final Hashtable<ModulePointer, ModuleRelatives> modRelHashtable = new Hashtable<>();

    void putRelatives(final ModulePointer modulePointer, final ModuleRelatives relatives) {
        modRelHashtable.put(modulePointer, relatives);
    } // end putRelatives()


    Enumeration<ModulePointer> getKeys() {
        return modRelHashtable.keys();
    }


    // Add the entries from otherMR into THIS; they are assumed not to overlap.
    void union(final ModuleRelationships otherMR) {

        final Enumeration<ModulePointer> otherKeys = otherMR.getKeys();

        while (otherKeys.hasMoreElements()) {
            final ModulePointer key = otherKeys.nextElement();

            if (key.getRelatives() == null) {
                this.putRelatives(key, key.getRelatives());
            }
        }

    } // end union()


    public String toString() {

        final StringBuilder ret = new StringBuilder();

        final Enumeration<ModulePointer> e = modRelHashtable.keys();
        while (e.hasMoreElements()) {

            final ModulePointer modPtr = e.nextElement();

            ret.append("\n----------- Module '").append(modPtr.getName()).append("'\n");
            ret.append(modPtr.getRelatives().toString());
            ret.append("-----------").append("\n");

        } // end while

        return ret.toString();

    } // end toString()

} // end class
