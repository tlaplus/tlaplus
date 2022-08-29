// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.xml.SymbolContext;
import util.UniqueString;

import java.util.Hashtable;

/**
 * A FormalParamNode represents a formal parameter in a user
 * definition--for example, p and q in
 * <p>
 * Foo(p, q(_)) == expr
 */

/***************************************************************************
 * The constructor adds the node to the SymbolTable specified as an         *
 * argument.                                                                *
 ***************************************************************************/
public class FormalParamNode extends SymbolNode {

    private final int arity;
    // arity of the parameter; 0 for ordinary param; >0 for operator param
    private final ModuleNode moduleNode;
    // the module in which this formal param was declared

    // Constructor
    public FormalParamNode(final UniqueString us, final int ar, final TreeNode stn,
                           final SymbolTable symbolTable, final ModuleNode mn) {
        super(FormalParamKind, stn, us);
        this.arity = ar;
        this.moduleNode = mn;
        if (symbolTable != null)     // null for fake formal params of built-in operators
            symbolTable.addSymbol(us, this);
    }

    /**
     * Returns the number of arguments this paramter takes when used in
     * an expression.
     */
    @Override
    public final int getArity() {
        return this.arity;
    }

    /* Returns true always.  */
    @Override
    public final boolean isLocal() {
        return true;
    }

    public final ModuleNode getModuleNode() {
        return this.moduleNode;
    }

    @Override
    public final boolean match(final OpApplNode test, final ModuleNode mn) {
        /***********************************************************************
         * True iff the current object has the same arity as the node operator  *
         * of the OpApplNode test.                                              *
         ***********************************************************************/
        final SymbolNode odn = test.getOperator();
        return odn.getArity() == this.arity;
    }



    /* Level checking */
//  private HashSet levelParams;

    @Override
    public final boolean levelCheck(final int iter) {
        if (levelChecked == 0) {
            /*********************************************************************
             * There's never any need to do this more than once.                  *
             *********************************************************************/
            levelChecked = iter;
            this.levelParams.add(this);
            this.allParams.add(this);
        }
        return true;
    }

    /**
     * toString, levelDataToString and walkGraph methods to implement
     * ExploreNode interface
     */

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (semNodesTable.get(uid) != null) return;

        semNodesTable.put(uid, this);
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";
        return ("\n*FormalParamNode: " + this.getName().toString() +
                "  " + super.toString(depth) + "  arity: " + arity);
    }

    @Override
    protected String getNodeRef() {
        return "FormalParamNodeRef";
    }

    @Override
    protected Element getSymbolElement(final Document doc, final SymbolContext context) {
        final Element e = doc.createElement("FormalParamNode");
        e.appendChild(appendText(doc, "uniquename", getName().toString()));
        e.appendChild(appendText(doc, "arity", Integer.toString(getArity())));
        return e;
    }
}
