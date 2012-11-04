// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import tla2sany.st.TreeNode;
import util.UniqueString;

/** 
 * Abstract class extended by classes that represent the meaning of an
 * identifier, including generalized IDs.  
 *
 * Extended by OpDefOrDeclNode (and its subclasses OpDefNode, OpDeclNode), 
 * FormalParamNode, and ModuleNode
 */

/***************************************************************************
* Also extended by NewSymbNode and ThmOrAssumpDefNode.                     *
***************************************************************************/

/***************************************************************************
* An object of superclass SymbolNode seems to represent something that     *
* defines or declares a symbol, and hence might appear in a SymbolTable.   *
* The constructors for these objects take a SymbolTable st as an argument  *
* and, if st is non-null, call st.addSymbol to put the symbol in the       *
* SymbolTable st.                                                          *
***************************************************************************/
public abstract class SymbolNode extends LevelNode {

  protected final UniqueString name;    // the name of this symbol
  
  SymbolNode(int kind, TreeNode stn, UniqueString name) {
    super(kind, stn);
    this.name = name;
  }
  
  /** 
   * This method returns the UniqueString for the printable name of
   * the symbol being declared or defined. For example, if this node
   * is an operator definition:                                                    
   *                                                                 
   *   Foo(a, b) == a*b                                              
   *                                                                 
   * getName() is the UniqueString for "Foo".
   */
  public final UniqueString getName() { return this.name; }

  /* Returns the arity of the operator named by the symbol.  */
  public abstract int getArity();

  /**
   * Returns true iff the symbol is local to its module; does not
   * apply to FormalParamNodes or ModuleNodes.
   */
  public abstract boolean isLocal();

  /**
   * Returns true iff the OpApplNode test has the proper types of
   * arguments for the operator as declared in module mn.
   */
  public abstract boolean match(OpApplNode test, ModuleNode mn) throws AbortException ;

  public final boolean occur(SymbolNode[] params) {
    for (int i = 0; i < params.length; i++) {
      if (this == params[i]) return true;
    }
    return false;
  }

  public final boolean isParam() {
    return (this instanceof OpDeclNode ||
	    this instanceof FormalParamNode);
  }
  
  /**
   * Returns true iff this node and otherNode are both OpDefOrDeclNode objects or
   * both ThmOrAssumpDefNode objects and have the same originallyDefinedInModule
   * field.  Added by LL on 31 Oct 2012. 
   * 
   * Corrected by LL on 1 Nov 2012 by (a) using the originallyDefinedInModule for
   * the source definitions (returned by getSource()), and by adding requirement 
   * that their module of origin has no parameters. 
   * 
   * This method is used to check that two instantiations of a definition
   * are the same.  They may not be if the two instantiations of their module have different
   * substitutions for parameters.  To check that the substitutions are the same
   * would be difficult, so we require that the module has no parameters.  This covers
   * the common case when the definitions come from a standard module.
   * 
   * @param otherNode
   * @return
   */
  public final boolean sameOriginallyDefinedInModule(SymbolNode otherNode) {     
      if (this.getClass() == otherNode.getClass()) {
          ModuleNode thisModule = null ;
          if (this instanceof OpDefNode) {
              OpDefNode thisSrc = ((OpDefNode) this).getSource() ;
              if (thisSrc != ((OpDefNode) otherNode).getSource()) {
                  return false;
              }
              thisModule  = ((OpDefNode) thisSrc).getOriginallyDefinedInModuleNode();
          }
          else if (this instanceof ThmOrAssumpDefNode) {
              ThmOrAssumpDefNode thisSrc = ((ThmOrAssumpDefNode) this).getSource() ;
              if (thisSrc != ((ThmOrAssumpDefNode) otherNode).getSource()) {
                  return false;
              }
              thisModule  = ((ThmOrAssumpDefNode) thisSrc).getOriginallyDefinedInModuleNode();
          }
          else {
              return false;
          }
          
          return   (thisModule == null)
                || (   (thisModule.getConstantDecls().length == 0)
                    && (thisModule.getVariableDecls().length == 0)) ;
      }
      return false ; // The compiler doesn't realize this is unreachable.
  }
}
