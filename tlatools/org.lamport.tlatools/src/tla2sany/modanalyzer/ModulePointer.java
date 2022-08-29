// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import tla2sany.st.TreeNode;

import java.util.ArrayList;

/**
 * An instance of this class is a "pointer" to a module used during
 * the loading of the various files that, through EXTENDS and
 * INSTANCE, become a single large multi-file spec.
 * <p>
 * A ModulePointer can point to any module, internal or top-level, in
 * any file (ParseUnit).
 */
public class ModulePointer {

    private final SpecObj spec;        // The SpecObj for the whole spec
    private final ParseUnit parseUnit;   // The ParseUnit (file) that the module is part of
    private final TreeNode treeNode;    // Must point to the TreeNode in the parse tree that contains the
    //   N_Module node at the head of a module
    private ModuleRelatives moduleRelatives; // Contains info on related modules (parent, inner, extends, instantiates)

    // Constructor
    ModulePointer(final SpecObj spec, final ParseUnit p, final TreeNode t) {
        this.spec = spec;
        this.parseUnit = p;
        this.treeNode = t;
    }

    // Returns the ParseUnit that this module is part of
    final ParseUnit getParseUnit() {
        return parseUnit;
    }


    // Returns the String name of this module
    final String getName() {
        return treeNode.heirs()[0].heirs()[1].getImage();
    }

    // Returns context for module referred to by THIS ModulePointer
    final ModuleContext getContext() {
        return moduleRelatives.context;
    } // end getContext()


    // Return the associated ModuleRelatives object
    public final ModuleRelatives getRelatives() {
        return moduleRelatives;
    }


    // Set the ModuleRelatives field
    final void putRelatives(final ModuleRelatives relatives) {
        moduleRelatives = relatives;
        spec.getModuleRelationships().putRelatives(this, relatives);
    }


    // Returns ArrayList of names of modules extended
    ArrayList<String> getNamesOfModulesExtended() {
        return moduleRelatives.directlyExtendedModuleNames;
    }


    // Returns ArrayList of names of modules instanced
    ArrayList<String> getNamesOfModulesInstantiated() {
        return moduleRelatives.directlyInstantiatedModuleNames;
    }


    // Returns ArrayList of names of Module pointers for immediate inner modules
    ArrayList<ModulePointer> getDirectInnerModules() {
        return moduleRelatives.directInnerModules;
    }


    // Returns reference to the N_Extends TreeNode heading the EXTENDS declaration (even if empty)
    TreeNode getExtendsDecl() {
        return treeNode.heirs()[1];
    }


    // Returns reference to the N_Body TreeNode heading the body of the module, (even if empty)
    TreeNode getBody() {
        return treeNode.heirs()[2];
    }


    // Returns a triple of the file name, the module name, and--to disambiguate among
    // inner modules with the same name--the treeNode value itself.
    public String toString() {
        return "ModulePointer (" + parseUnit.getFileName() + ",$" + this.getName() + "," + treeNode + ")\n" +
                "Relatives:\n" + moduleRelatives.toString();
    }

    public String toStringAbbrev() {
        return "ModPtr(" + parseUnit.getFileName() + ",$" + this.getName() + "," + treeNode + ")\n";
    }
}
