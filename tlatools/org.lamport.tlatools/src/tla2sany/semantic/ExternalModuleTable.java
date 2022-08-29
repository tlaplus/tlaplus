// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// Last modified on Sat 17 Mar 2007 at 11:28:08 PST by lamport
/***************************************************************************
 * 2 Mar 2007: enum <- Enum                                                 *
 ***************************************************************************/

package tla2sany.semantic;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.utilities.Strings;
import util.UniqueString;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;

public class ExternalModuleTable implements ExploreNode {

    /*************************************************************************
     * I presume the comment above is really about the HashTable              *
     * moduleHashTable, and that each of its entries has a moduleName as the  *
     * key and a value that's an ExternalModuleTableEntry object.             *
     *************************************************************************/
    public final Hashtable<UniqueString, ExternalModuleTableEntry> moduleHashTable;

    // Each entry in the Hashtable "ht" is a tuple of the form
    //
    //   (moduleName, <context, ModuleNode>)
    //
    // where the moduleName is the hash key.  The modules included are
    // the root module, and all of those other top-level (i.e. external)
    // modules it depends upon, directly or indirectly, by EXTENDS or
    // INSTANCE (but NOT including internal modules)
    // ArrayList moduleArrayList contains ModuleNodes (the same ones as
    // moduleHashTable), but preserves the order in which they were
    // inserted.  If module A depends on module B, then A has a HIGHER
    // index than B.
    public final ArrayList<ModuleNode> moduleNodeArrayList;
    // The nodule node of the root module
    public ModuleNode rootModule;

    // Constructor
    public ExternalModuleTable() {
        moduleHashTable = new Hashtable<>();
        moduleNodeArrayList = new ArrayList<>();
    }

    // Set and get the rootModule field
    public ModuleNode getRootModule() {
        return rootModule;
    }

    public void setRootModule(final ModuleNode mn) {
        rootModule = mn;
    }

    public final Context getContext(final UniqueString key) {
        final ExternalModuleTableEntry p = moduleHashTable.get(key);
        if (p == null) return null;
        return p.ctxt;
    }

    public final Context getContextForRootModule() {
        return getContext(getRootModule().getName());
    }

    /**
     * Returns a ArrayList of ModuleNodes, one for each outer module (i.e. not
     * inner modules) in the specification.  InnerModules can be obtained
     * via getInnerModules() applied to a ModuleNode.
     * <p>
     * The modules are ordered so that if module A EXTENDS or INSTANCE's
     * module B, then A has a higher index than B in the array.
     */
    public ModuleNode[] getModuleNodes() {
        final ModuleNode[] mods = new ModuleNode[moduleNodeArrayList.size()];
        for (int i = 0; i < mods.length; i++) {
            mods[i] = moduleNodeArrayList.get(i);
        }
        return mods;
    }

    public final ModuleNode getModuleNode(final String key) {
        return getModuleNode(UniqueString.of(key));
    }

    public final ModuleNode getModuleNode(final UniqueString key) {
        final ExternalModuleTableEntry p = moduleHashTable.get(key);
        if (p == null) return null;
        return p.moduleNode;
    }

    public final void put(final UniqueString key, final Context ctxt, final ModuleNode moduleNode) {
        final ExternalModuleTableEntry c = moduleHashTable.get(key);
        if (c == null) {
            moduleHashTable.put(key, new ExternalModuleTableEntry(ctxt, moduleNode));
            moduleNodeArrayList.add(moduleNode);
        }
    }

    @Override
    public String toString() {
        final Enumeration<ExternalModuleTableEntry> Enum = moduleHashTable.elements();
        final StringBuilder ret = new StringBuilder();

        while (Enum.hasMoreElements()) {
            final ExternalModuleTableEntry mte = Enum.nextElement();
            ret.append(mte.toString());
        }
        return "\nModule Table:" + Strings.indent(2, ret.toString());
    }

    public void printExternalModuleTable(final int depth, final boolean b) {
        System.out.print("\nExternal Module Table:");

        for (final ModuleNode mn : moduleNodeArrayList) {
            if (mn != null) {
                System.out.print(Strings.indent(2, "\nModule: "));
                mn.print(2, depth, b);
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
    @Override
    public String levelDataToString() {
        return "Dummy level string";
    }

    @Override
    public String toString(final int depth) {
        if (depth <= 0) return "";

        final StringBuilder ret = new StringBuilder();
        for (final ModuleNode mn : moduleNodeArrayList) {
            if (mn != null) {
                ret.append(Strings.indent(2, "\nModule: " + Strings.indent(2, mn.toString(depth))));
            } else {
                final String str = "\n***Null ExternalModuleTable entry; module contained error and was not created.";
                ret.append(Strings.indent(2, "\nModule: " + Strings.indent(2, str)));
            }
        }
        return ret.toString();
    }

    public void walkGraph(final Hashtable<Integer, ExploreNode> moduleNodesTable) {
        walkGraph(moduleNodesTable, ExplorerVisitor.NoopVisitor);
    }

    @Override
    public void walkGraph(final Hashtable<Integer, ExploreNode> moduleNodesTable, final ExplorerVisitor visitor) {
        final Enumeration<ExternalModuleTableEntry> Enum = moduleHashTable.elements();

        while (Enum.hasMoreElements()) {
            final ExternalModuleTableEntry mte = Enum.nextElement();
            mte.walkGraph(moduleNodesTable, visitor);
        }
    }

    public static class ExternalModuleTableEntry implements ExploreNode {

        final ModuleNode moduleNode;  // the ModuleNode
        final Context ctxt;        // and its full context, including all Builtin ops, ops from EXTENDS and INSTANCE,
        //   and module nodes for inner modules (but NOT its defined ops)

        ExternalModuleTableEntry(final Context ctxt, final ModuleNode modn) {
            this.ctxt = ctxt;
            this.moduleNode = modn;
        }

        public ModuleNode getModuleNode() {
            return moduleNode;
        }

        public void printMTE(final int depth, final boolean b) {
            if (moduleNode != null) {
                System.out.print(Strings.indent(2, "\nModule: "));
                moduleNode.print(2, depth, b);
            } else {
                System.out.print(Strings.indent(2, "\nModule: " +
                        Strings.indent(2, "\n***Null ExternalModuleTable entry; " +
                                "module contained error and was not created."))
                );
            }
        } // end printMTE()

        /**
         * walkGraph, levelDataToString, and toString methods to implement ExploreNode interface
         */
        @Override
        public String levelDataToString() {
            return "Dummy level string";
        }

        @Override
        public void walkGraph(final Hashtable<Integer, ExploreNode> moduleNodesTable, final ExplorerVisitor visitor) {
            if (moduleNode != null) moduleNode.walkGraph(moduleNodesTable, visitor);
            if (ctxt != null) ctxt.walkGraph(moduleNodesTable, visitor);
        } // end walkGraph()

        @Override
        public String toString(final int depth) {
            if (depth <= 0) return "";

            if (moduleNode != null) {
                return Strings.indent(2, "\nModule: " + Strings.indent(2, moduleNode.toString(depth)));
            } else {
                return Strings.indent(2, "\nModule: " + Strings.indent(2, "\n***Null ExternalModuleTable entry; " +
                        "module contained error and was not created."));
            }
        } // end toString()

    } // end internal class ModuleTableEntry

}
