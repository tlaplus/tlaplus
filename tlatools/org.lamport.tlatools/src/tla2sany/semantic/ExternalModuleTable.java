// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// Last modified on Sat 17 Mar 2007 at 11:28:08 PST by lamport
/***************************************************************************
* 2 Mar 2007: enum <- Enum                                                 *
***************************************************************************/

package tla2sany.semantic;

import java.util.Enumeration;
import java.util.Hashtable;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;
import util.UniqueString;

public class ExternalModuleTable implements ExploreNode {

  public class ExternalModuleTableEntry implements ExploreNode {

    ModuleNode   moduleNode;  // the ModuleNode
    Context      ctxt;        // and its full context, including all Builtin ops, ops from EXTENDS and INSTANCE,
                              //   and module nodes for inner modules (but NOT its defined ops)

    ExternalModuleTableEntry (Context ctxt, ModuleNode modn) {
      this.ctxt = ctxt;
      this.moduleNode = modn;
    } 

    public ModuleNode getModuleNode() { return moduleNode; }

    public void printMTE(int depth, boolean b) {
      if (moduleNode != null) {
        System.out.print(Strings.indent(2, "\nModule: ")); 
        moduleNode.print(2,depth,b);
      }
      else {
        System.out.print(Strings.indent(2, "\nModule: " + 
                         Strings.indent(2, "\n***Null ExternalModuleTable entry; " + 
                                           "module contained error and was not created."))
                        );
      }
    } // end printMTE()

    /**  
     * walkGraph, levelDataToString, and toString methods to implement ExploreNode interface
     */
    public String levelDataToString() { return "Dummy level string"; }

    public void walkGraph(Hashtable<Integer, ExploreNode> moduleNodesTable, ExplorerVisitor visitor) {
      if (moduleNode != null)   moduleNode.walkGraph(moduleNodesTable, visitor);
      if (ctxt != null)      ctxt.walkGraph(moduleNodesTable, visitor);
    } // end walkGraph()

    public String toString(int depth) {
      if (depth <= 0) return "";
      
      if (moduleNode != null) {
	return Strings.indent(2, "\nModule: " + Strings.indent(2,moduleNode.toString(depth)) );
      } else {
	return Strings.indent(2, "\nModule: " + Strings.indent(2, "\n***Null ExternalModuleTable entry; " + 
							       "module contained error and was not created."));
      }
    } // end toString()

  } // end internal class ModuleTableEntry

  // Each entry in the Hashtable "ht" is a tuple of the form
  //
  //   (moduleName, <context, ModuleNode>)
  //
  // where the moduleName is the hash key.  The modules included are
  // the root module, and all of those other top-level (i.e. external)
  // modules it depends upon, directly or indirectly, by EXTENDS or
  // INSTANCE (but NOT including internal modules)
  /*************************************************************************
  * I presume the comment above is really about the HashTable              *
  * moduleHashTable, and that each of its entries has a moduleName as the  *
  * key and a value that's an ExternalModuleTableEntry object.             *
  *************************************************************************/
  public Hashtable<UniqueString, ExternalModuleTableEntry> moduleHashTable;

  // Vector moduleVector contains ModuleNodes (the same ones as
  // moduleHashTable), but preserves the order in which they were
  // inserted.  If module A depends on module B, then A has a HIGHER
  // index than B.
  public Vector<ModuleNode>    moduleNodeVector;

  // The nodule node of the root module
  public ModuleNode rootModule;

  // Constructor
  public ExternalModuleTable() {
    moduleHashTable  = new Hashtable<>();
    moduleNodeVector = new Vector<>();
  }

  // Set and get the rootModule field
  public ModuleNode getRootModule()              { return rootModule; }
  public void       setRootModule(ModuleNode mn) { rootModule = mn; }

  public final Context getContext( UniqueString key ) {
    ExternalModuleTableEntry p = moduleHashTable.get(key);
    if (p == null) return null;
    return p.ctxt;
  }

  public final Context getContextForRootModule() {
	  return getContext(getRootModule().getName());
  }
  
  /**
   *  Returns a vector of ModuleNodes, one for each outer module (i.e. not
   *  inner modules) in the specification.  InnerModules can be obtained 
   *  via getInnerModules() applied to a ModuleNode.
   *
   *  The modules are ordered so that if module A EXTENDS or INSTANCE's
   *  module B, then A has a higher index than B in the array.
   */
  public ModuleNode[] getModuleNodes() {
    ModuleNode [] mods = new ModuleNode[moduleNodeVector.size()];
    for (int i = 0; i < mods.length; i++) {
      mods[i] = (ModuleNode)moduleNodeVector.elementAt(i);
    }
    return mods;
  }

  public final ModuleNode getModuleNode( String key ) {
	  return getModuleNode(UniqueString.of(key));
  }

  public final ModuleNode getModuleNode( UniqueString key ) {
    ExternalModuleTableEntry p = moduleHashTable.get(key);
    if (p == null) return null;
    return p.moduleNode;
  }

  public final void put( UniqueString key, Context ctxt, ModuleNode moduleNode ) {
    ExternalModuleTableEntry c = moduleHashTable.get( key );
    if (c == null) {
      moduleHashTable.put( key, new ExternalModuleTableEntry(ctxt, moduleNode) );
      moduleNodeVector.addElement(moduleNode);
    }
  }

  @Override
  public String toString() {
    Enumeration<ExternalModuleTableEntry> Enum = moduleHashTable.elements();
    String ret = "";

    while (Enum.hasMoreElements()) {
      ExternalModuleTableEntry mte = Enum.nextElement();
      ret = ret + mte.toString();
    }
    return "\nModule Table:" + Strings.indent(2,ret);
  }

  public void printExternalModuleTable(int depth, boolean b) {
    System.out.print("\nExternal Module Table:");

    for (int i = 0; i < moduleNodeVector.size(); i++) {
      ModuleNode mn = moduleNodeVector.elementAt(i);

      if (mn != null) {
        System.out.print(Strings.indent(2, "\nModule: ")); 
        mn.print(2,depth,b);
      } else {
        System.out.print(Strings.indent(2, "\nModule: " + 
                         Strings.indent(2, "\n***Null ExternalModuleTable entry; " + 
                                           "module contained error and was not created.")));
      }
    }
  }

  /**  
   * walkGraph, levelDataToString, and toString methods to implement ExploreNode interface
   */
  public String levelDataToString() { return "Dummy level string"; }

  public String toString(int depth) {
    if (depth <= 0) return "";

    String ret = "";
    for (int i = 0; i < moduleNodeVector.size(); i++) {
      ModuleNode mn = (ModuleNode)moduleNodeVector.elementAt(i);
      if (mn != null) {
        ret += Strings.indent(2, "\nModule: " + Strings.indent(2, mn.toString(depth)) );
      } else {
	String str = "\n***Null ExternalModuleTable entry; module contained error and was not created.";
	ret += Strings.indent(2, "\nModule: " + Strings.indent(2, str));
      }
    }
    return ret;
  }

  public void walkGraph(Hashtable<Integer, ExploreNode> moduleNodesTable) {
	  walkGraph(moduleNodesTable, ExplorerVisitor.NoopVisitor);
  }

  public void walkGraph(Hashtable<Integer, ExploreNode> moduleNodesTable, ExplorerVisitor visitor) {
    Enumeration<ExternalModuleTableEntry> Enum = moduleHashTable.elements();

    while ( Enum.hasMoreElements() ) {
	ExternalModuleTableEntry mte = Enum.nextElement();
	mte.walkGraph(moduleNodesTable, visitor);
    }
  }

}
