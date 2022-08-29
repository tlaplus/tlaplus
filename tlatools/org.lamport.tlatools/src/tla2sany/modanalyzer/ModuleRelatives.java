// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import java.util.ArrayList;

/**
 * This class contains fields representing the names of modules that are all related by EXTENDing or INSTANCEing
 * or inner definition to a ParseUnit (i.e. top level module in its own file)
 */
public class ModuleRelatives {

    final ParseUnit parseUnit;                              // The ParseUnit that THIS ModuleRelatives object is associated with

    final ModulePointer currentModule; // The TreeNode where the name of the current module appears in
    //   in the image field; using the tree node rather than the String
    //   name of the module
    final ArrayList<ModulePointer> directInnerModules = new ArrayList<>();
    //   null currentModule is the outermost in parseUnit
    final ArrayList<String> directlyExtendedModuleNames = new ArrayList<>();
    // ArrayList of ModulePointers for immediate inner modules
    final ArrayList<String> directlyInstantiatedModuleNames = new ArrayList<>();
    // ArrayList of String names for modules mentioned in EXTENDS decls by
    //   currentModule, whether or not they are resolved within the
    //   current ParseUnit
    final ModuleContext context = new ModuleContext();          // The context that maps module String names known in this module
    // ArrayList of String names for modules directly instantiated
    //   by currentModule, whether or not they are resolved within the
    //   current ParseUnit
    ModulePointer outerModule = null; // TreeNode of the immediate outer (parent) module;
    //   (whether or not they are referenced in it) to ModulePointers


    // constructor
    public ModuleRelatives(final ParseUnit pu, final ModulePointer node) {
        parseUnit = pu;
        currentModule = node;
    }

    public String toString() {
        final StringBuilder ret = new StringBuilder("currentModuleName: " + currentModule.getName());

        ret.append("\nouterModule: ").append(outerModule == null
                ? "<null>"
                : outerModule.getName());

        ret.append("\ndirectInnerModules: ");
        for (ModulePointer directInnerModule : directInnerModules) {
            ret.append(directInnerModule.getName()).append(" ");
        }

        ret.append("\ndirectlyExtendedModuleNames: ");
        for (String directlyExtendedModuleName : directlyExtendedModuleNames) {
            ret.append(directlyExtendedModuleName).append(" ");
        }

        ret.append("\ndirectlyInstantiatedModuleNames: ");
        for (String directlyInstantiatedModuleName : directlyInstantiatedModuleNames) {
            ret.append(directlyInstantiatedModuleName).append(" ");
        }

        ret.append("\n").append(context);
        return ret.toString();
    }

    public void addExtendee(final String module) {
        directlyExtendedModuleNames.add(module);
    }
} // end class
