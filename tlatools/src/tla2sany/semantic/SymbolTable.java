// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import tla2sany.utilities.Stack;
import tla2sany.utilities.Vector;
import util.UniqueString;

// The Symbol Table builds the stack of context tables.  The stack
// model for symbol resolution is straightforward, but not
// necessarily very efficient as we may create and push a lot of
// contexts as inner modules contexts, LET expression contexts, bound
// variable contexts, and formal parameter contexts.

// The context at the bottom of the stack initially is a copy of the
// built-in symbols.  All top level definitions of the module will be
// added to it, to become eventually the global context of this
// module (including symbols added by Extends and Instance)

public class SymbolTable implements ASTConstants {

   
  private Stack               contextStack;  
     // A SymbolTable is a stack of contexts.  New contexts are
     // pushed on the stack for LET, for formal param lists, 
     // for bound variables sets, and for inner modules
  private Context             topContext;    
     // The top context on the stack
  private Context             baseContext;   
    // The bottom context on the stack; holds builtin op symbols
    //   and also all top-level symbols of External module
  private ExternalModuleTable mt;            
    // The ExternalModuleTable for the spec to which THIS
    //   SymbolTable and its external module belongs
  private ModuleNode          modNode;       
    // The ModuleNode of the module (internal or external)
    //   with which THIS SymbolTable is associated
  private Errors              errors;        
    // The Errors object to which error messages involving
    //   THIS SymbolTable should be appended.

  // This form for external modules
  public SymbolTable( ExternalModuleTable mt, Errors errs ) {
    // Makes copy of context containing built-in symbols:
    topContext = Context.getGlobalContext().duplicate(mt);
    baseContext = topContext;

    errors = errs;
    contextStack = new Stack();
    contextStack.push( topContext );
    this.mt = mt;
  };

  // This form for internal modules
  public SymbolTable(ExternalModuleTable mt, Errors errs, SymbolTable st) {
    modNode = st.modNode;
    errors = errs;
    contextStack = new Stack();
    for (int i = 0; i < st.contextStack.size(); i++) {
      contextStack.push( st.contextStack.elementAt( i ) );
    }
    baseContext = (Context)contextStack.elementAt(0);
    this.mt = mt;
  }

  // Return the Outer context for this external module, i.e. builtin symbols,
  // and all symbols declared or defined in that module (but not in inner
  // modules, or param lists, or bound var lists, or LET clauses)
  public final Context getExternalContext() { return baseContext; }

  public final Context getContext() { return topContext; }

  public final void pushContext( Context ct ) {
    contextStack.push( ct ); 
    topContext = ct;
  }

  public final void popContext() {
    contextStack.pop();
    topContext = (Context) contextStack.peek();
  }

  public final void setModuleNode(ModuleNode mn) { modNode = mn; }

  public final ModuleNode getModuleNode() { return this.modNode; }

  /*************************************************************************
  * Looks up `name' in the symbol table and returns the node it finds, or  *
  * null if there is no entry for `name'.                                  *
  *************************************************************************/
  public final SymbolNode resolveSymbol(UniqueString name) {
    for (int c = contextStack.size()-1; c >= 0; c-- ) {
      Context ct = (Context)contextStack.elementAt(c);
      SymbolNode r = ct.getSymbol( name );
      if (r != null) return r;
    }
    return null;
  }

  public final ModuleNode resolveModule(UniqueString name) {
    ModuleName modName = new ModuleName(name);

    for (int c = contextStack.size()-1; c >= 0; c--) {
      Context ct = (Context)contextStack.elementAt(c);
      SymbolNode res = ct.getSymbol(modName);
      if (res != null) return (ModuleNode)res;
    }

    // See if "name" refers to an external module
    return mt.getModuleNode(name);
  }
  
  /**
   * The addSymbol method attempts to bind the name "name" to the
   * SymbolNode "symbol" in THIS SymbolTable, and returns true if that
   * succeeds, i.e. if the name was previously unbound, or if the
   * declaration causing symbol to be bound to "name" is the same
   *
   * In other cases, it appends a message to "errors" and returns false.
   * 
   * As of 31 Oct 2012, the return value was not used by any calling method.
   */
  public final boolean addSymbol(UniqueString name, SymbolNode symbol) {
    SymbolNode currentBinding = resolveSymbol(name);
// System.out.println("*** Resolving " + name.toString() + ", in binding ");
    // If "name" is already bound to the argument "symbol", then
    // nothing needs to be done; this call is redundant
    if (currentBinding == symbol) { return true; }
// System.out.println("*** No matching same symbol " + name.toString());

    // If "name" was not already present in THIS SymbolTable, then add
    // it and bind it to "symbol"
    if (currentBinding == null)  { 
      topContext.addSymbolToContext(name, symbol);
      return true;
    }

// System.out.println("*** Was found in symbol table " + symbol.getKind());

    // If the currentBinding is to a different SymbolNode that does
    // not have the same kind or arity as "symbol" then this is
    // definitely an erroneous duplicate definition.  Also, even if it
    // *IS* the same kind and arity, if we are attempting to bind a
    // name to a FormalParamNode when that name has already been used
    // then that is an error, since formal param names must be "new".
    if (symbol.getKind() == FormalParamKind ||
	symbol.getKind() == BoundSymbolKind ||
	currentBinding.getKind() != symbol.getKind() ||
        currentBinding.getArity() != symbol.getArity()) {
      errors.addError(symbol.getTreeNode().getLocation(),
		      "Multiply-defined symbol '" + name +
                      "': this definition or declaration conflicts \nwith the one at " +
                      currentBinding.getTreeNode().getLocation().toString() + ".");
      return false;
    }
// System.out.println("*** Was found in symbol table " + symbol.getKind());
 
    // If the symbol being redefined is a built-in symbol, this is definitely an error
    if (currentBinding.getTreeNode().getLocation().source().equals("--TLA+ BUILTINS--")) {
      errors.addError(symbol.getTreeNode().getLocation(),
		      "Symbol " + name + " is a built-in operator, and cannot be redefined.");  
      return false;
    } 

// The following test is misguided. The problem we need to worry about is merging symbols
// from the same module twice or more through EXTENDS or INSTANCE. Not multiple definitions.

    // If "name" resolves to a different SymbolNode than "symbol", 
    // but of the same kind and arity, and is not a FormalParamNode,
    // then we must test to see if the new definition 
    // is the "same" definition or "different".

// System.out.println("*** We made it here " + symbol.getKind());
    // If the two decls or defs of the same name originate in the same
    // original, parameter-free external module, then they are clearly
    // "the same" and no error or warning is necessary.
//     if (symbol instanceof OpDefOrDeclNode &&
//         ((OpDefOrDeclNode)symbol).getOriginallyDefinedInModuleNode() == 
// 	((OpDefOrDeclNode)currentBinding).getOriginallyDefinedInModuleNode() &&
// 	((OpDefOrDeclNode)currentBinding).getOriginallyDefinedInModuleNode().isParameterFree()) {
//       return true;
//     }

// System.out.println("*** Not legitimate duplicate " + symbol.getKind());
    /*
    // Debug
    System.out.println("\nsymbol '" + symbol.getName() + "' originally defined in: " + 
                       ((OpDefOrDeclNode)symbol).getOriginallyDefinedInModuleNode().getName() +
                       "\ncurrentBinding '" + currentBinding.getName() + "' originally defined in: " +
                       ((OpDefOrDeclNode)currentBinding).getOriginallyDefinedInModuleNode().getName() );
    System.out.println("Module '" +
		       ((OpDefOrDeclNode)currentBinding).getOriginallyDefinedInModuleNode().getName() +
		       "' parameter free?  " +
		       ((OpDefOrDeclNode)currentBinding).getOriginallyDefinedInModuleNode().isParameterFree());
    */
    

    // If we survive the above tests, however, then this is a case of
    // multiple definitions.  We report this as a warning unless both definitions
    // come from the same module.  
    // Test for same module added by LL on 31 Oct 2012 to fix problem caused by
    // the same module being both EXTENDed and imported with a LOCAL INSTANCE.  
    // Previously, it always added the warning.
    if (symbol.sameOriginallyDefinedInModule(currentBinding)) {
        return true ;
    }
    errors.addWarning(symbol.getTreeNode().getLocation(), 
		      "Multiple declarations or definitions for symbol " + name +
		      ".  \nThis duplicates the one at " +
		      currentBinding.getTreeNode().getLocation().toString()
		      + "."
		      // This part of message commented out by LL on 24 Oct 2009
//		      The original declaration or definition will be used, " +
//		      "and this one will be ignored." 
		      ); 

    return true; 
  } // end addSymbol() 

  public final boolean addModule(UniqueString name, ModuleNode symbol) {
    SymbolNode currentBinding = resolveModule(name);

    // If "name" is already bound to the argument "symbol", then
    // nothing needs to be done; this call is redundant
    if (currentBinding == symbol) { return true; }

    // If "name" was not already present in THIS SymbolTable, then add
    // it and bind it to "symbol"
    if (currentBinding == null)  {
      ModuleName modName = new ModuleName(name);
      topContext.addSymbolToContext(modName, symbol);
      return true;
    }

    errors.addError(symbol.getTreeNode().getLocation(),
		    "Multiply-defined module '" + name +
		    "': this definition or declaration conflicts \nwith the one at " +
		    currentBinding.getTreeNode().getLocation().toString() + ".");
    return false;
  }
  
  // return a string with all symbols in all contexts, from top to bottom
  public String toString() {
    String ret = "\n\n***SymbolTable\n\n*** top context";

    for (int c = contextStack.size()-1; c >= 0; c--) {
      Context ct = (Context) contextStack.elementAt(c);
      Vector v = ct.getContextEntryStringVector(1,true);

      for (int i = 0; i < v.size(); i++) {
        ret += (String)v.elementAt(i);
      }
      ret += "\n\n*** next context\n";
    }
    return ret; 
  }

  static class ModuleName {
    UniqueString name;

    ModuleName(UniqueString name) {
      this.name = name;
    }

    public final int hashCode() { return this.name.hashCode(); }

    public final boolean equals(Object obj) {
      return ((obj instanceof ModuleName) &&
	      this.name.equals(((ModuleName)obj).name));
    }

    public final String toString() {
      return this.name.toString();
    }
	
  }
  
}
