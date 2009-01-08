// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import java.util.Enumeration;
import java.util.Hashtable;

/**
 * Each instance of this class basically is a map from ModulePointer objects to
 * ModuleRelatives objects.
 *
 * It is primarily a wrapper for a Hashtable, with the added benefit of type checking
 */

class ModuleRelationships {

  // Maps ModulePointer objects to ModuleRelatives objects
  private Hashtable modRelHashtable = new Hashtable();

/*
  ModuleRelatives getRelatives(ModulePointer modulePointer) { 
    return modulePointer.getRelatives(); //(ModuleRelatives)modRelHashtable.get(modulePointer); 
  }
*/

  void putRelatives (ModulePointer modulePointer, ModuleRelatives relatives) {
    modRelHashtable.put(modulePointer, relatives);
  } // end putRelatives()


  ModuleContext getContext(ModulePointer module) {
    return module.getRelatives().context;
  } // end getContext()


  Enumeration getKeys() { return modRelHashtable.keys(); }  


  // Add the entries from otherMR into THIS; they are assumed not to overlap.
  void union(ModuleRelationships otherMR) {

    Enumeration otherKeys = otherMR.getKeys();

    while ( otherKeys.hasMoreElements() ) {
      ModulePointer key = (ModulePointer)otherKeys.nextElement();

      if (key.getRelatives() == null ) { 
        this.putRelatives( key, key.getRelatives() );
      }
    }

  } // end union()


  public String toString() {

    String ret = "";

    Enumeration e = modRelHashtable.keys();
    while ( e.hasMoreElements()) {

      ModulePointer   modPtr    = (ModulePointer)e.nextElement();

      ret = ret + "\n----------- Module '" + modPtr.getName() + "'\n";
      ret = ret + modPtr.getRelatives().toString(); 
      ret = ret + "-----------" + "\n";  

    } // end while 

    return ret;

  } // end toString()

} // end class
