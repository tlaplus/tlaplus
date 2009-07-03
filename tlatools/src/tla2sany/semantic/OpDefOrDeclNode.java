// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import tla2sany.st.TreeNode;
import util.UniqueString;

/**
 * A OpDefOrDeclNode represents the definition or declaration of
 * a symbol.  (For some symbols, it represents an imaginary          
 * definition.)  It has two subclasses, OpDeclNode and OpDefNode.    
 */
    
public abstract class OpDefOrDeclNode extends SymbolNode {

  ModuleNode originallyDefinedInModule;
     // The (external or inner) module in which this operator def or decl  
     // originally appears in (as opposed to having been inherited via
     // EXTENDS or INSTANCE-without-params).  A null in this field
     // means either that this is the OpDefNode for a built-in
     // operator, or that this is a nullODN node as declared in 
     // semantic.Generator.
  SymbolTable st;
    /***********************************************************************
    * For an OpDeclNode, this seems to contain the SymbolTable under       *
    * which it was generated.  This SymbolTable does not appear to be      *
    * used.  A comment in Generator.java asserts that, for an OpDecl node, *
    * it contains the formal parameters, but that comment appears to be    *
    * wrong.                                                               *
    ***********************************************************************/

  int arity;          // arity of -1 means no fixed arity, -2 is illegal

  public OpDefOrDeclNode(UniqueString name, int kind, int ar, ModuleNode modNode,
                         SymbolTable symbolTable, TreeNode stn ) {
    super(kind, stn, name);
    this.originallyDefinedInModule = modNode;
    this.arity = ar;
    this.st = symbolTable;
  }

  /**
   * This method returns the number of ordinary arguments--that is, the
   * arguments not part of the bound variable stuff.  For example, the 
   * $BoundedForAll operator has a single ordinary argument.           
   *                                                                   
   * If nA and nB are the nodes (of kind ConstantDeclKind) for the     
   * declarations of A and B in                                        
   *                                                                   
   *   CONSTANT  A, B(_,_)                                             
   *                                                                   
   * then nA.getNumberOfArgs() = 0 and nB.getNumberOfArgs() = 2.       
   *                                                                   
   * A VariableDecl or BoundSymbolKind node has getNumberOfArgs() equal
   * to 0.                                                             
   *                                                                   
   * For an operator like $CartesianProd that has a variable number of
   * arguments, this method returns the value -1.  Only BuiltIn nodes
   * (nodes of kind BuiltInKind) should have getNumberOfArgs equal to
   * -1.
   */
  public final int getNumberOfArgs() { return this.arity; }

  public final void setNumberOfArgs(int a) { this.arity = a; }

  public final ModuleNode getOriginallyDefinedInModuleNode() {
    return this.originallyDefinedInModule;
  }

  public final SymbolTable getSymbolTable() { return this.st; }

  /**
   * toString() method; part of implementation of ExploreNode
   * interface
   */
  public String toString(int depth) {
    if (depth <= 0) return "";
    return super.toString(depth) 
           + "  arity: " + arity 
           + "  orgDefInModule: " + (originallyDefinedInModule != null 
                             ? originallyDefinedInModule.getName().toString() 
                             : "<null>" );
  }
  
}
