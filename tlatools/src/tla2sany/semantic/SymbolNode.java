// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import tla2sany.st.TreeNode;
import util.UniqueString;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

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


  /** TL
   * Symbol nodes are exported using their names only. Within a context element,
   * we want to expand their whole definitions and are using this method
   * we need to add location and level information here.
   */
  public Element exportDefinition(Document doc,SemanticNode.SymbolContext context) {
    try {
      Element e = getSymbolElement(doc, context);
      // level
      try {
        Element l = appendText(doc,"level",Integer.toString(getLevel()));
        e.insertBefore(l,e.getFirstChild());
      } catch (RuntimeException ee) {
        // not sure it is legal for a LevelNode not to have level, debug it!
      }
      //location
      try {
        Element loc = getLocationElement(doc);
        e.insertBefore(loc,e.getFirstChild());
      } catch (RuntimeException ee) {
        // do nothing if no location
      }
      return e;
    } catch (RuntimeException ee) {
      System.err.println("failed for node.toString(): " + toString() + "\n with error ");
      ee.printStackTrace();
      throw ee;
    }
  }

  protected abstract Element getSymbolElement(Document doc,SemanticNode.SymbolContext context);
  protected abstract String getNodeRef();

  /** TL
   * we also override getLevelElement as it should never be called
   */
  protected Element getLevelElement(Document doc,SemanticNode.SymbolContext context) {
    throw new UnsupportedOperationException("This should not be possible and therefore a bug");
  }

  /** TL
   * We override export in order not to export location and level.
   * We only export names.
   */
  public Element export(Document doc,SemanticNode.SymbolContext context) {
    // first add symbol to context
    context.put(getName().toString(),this);
    Element e = doc.createElement(getNodeRef());
    e.appendChild(appendText(doc,"uniquename",getName().toString()));
    return e;
  }
}
