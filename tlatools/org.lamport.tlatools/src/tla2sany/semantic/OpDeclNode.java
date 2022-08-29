// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// last modified on Sat 28 June 2008 at  0:39:10 PST by lamport

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
 * An OpDeclNode can have one of the following kinds:
 * <p>
 * ConstantDeclKind
 * Represents a constant declaration, such as the C in
 * CONSTANTS B, C, D
 * <p>
 * VariableDeclKind
 * Represents a variable declaration, such as the y in
 * VARIABLES x, y, z
 * <p>
 * BoundSymbolKind
 * Represents a bound symbol such as the b in \E a, b \in S : P
 */

/***************************************************************************
 * Additional kinds added by LL on 22 Mar 2007:                             *
 *                                                                          *
 *   NewConstantKind                                                        *
 *   NewVariableKind                                                        *
 *   NewStateKind                                                           *
 *   NewActionKind                                                          *
 *   NewTemporalKind                                                        *
 *                                                                          *
 * Each represents a declaration in the ASSUME part of an ASSUME/PROVE.     *
 ***************************************************************************/

public class OpDeclNode extends OpDefOrDeclNode {

// Now a field in all subclasses of LevelNode
//  private int level;

    /*************************************************************************
     * The constructor.                                                       *
     *************************************************************************/
    public OpDeclNode(final UniqueString us, final int kind, final int level,
                      final int arity, final ModuleNode mn, final SymbolTable symbolTable,
                      final TreeNode stn) {
        super(us, kind, arity, mn, symbolTable, stn);
        this.level = level;
        if (this.getKind() == ConstantDeclKind) {
            this.levelParams.add(this);
            this.allParams.add(this);
        }
        this.levelChecked = 1;
        if (st != null) {
            st.addSymbol(us, this);
        }
    }

    /**
     * Constants and variables are never declared to be LOCAL
     * Their scope may *be* local (as with LET, or bound variables, or
     * in inner modules), but the LOCAL modifier is not used.
     */
    @Override
    public final boolean isLocal() {
        return false;
    }

    @Override
    public final int getArity() {
        return this.arity;
    }

    @Override
    public final boolean match(final OpApplNode oa, final ModuleNode mn) {
        final ExprOrOpArgNode[] args = oa.getArgs();

        if (args == null || arity != args.length) {
            errors.get().addError(oa.getTreeNode().getLocation(),
                    "Operator used with the wrong number of arguments.");
            return false;
        }
        return true;
    }

    /* Level checking */

//  private HashSet levelParams;

    @Override
    public final boolean levelCheck(final int iter) {
        /***********************************************************************
         * Level information set by constructor.                                *
         ***********************************************************************/
        return true;
    }


    /**
     * walkGraph, levelDataToString, and toString methods to implement
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
    public String getHumanReadableImage() {
        if (getKind() == 2) {
            return super.getName().toString() + " CONSTANT";
        } else if (getKind() == 3) {
            return super.getName().toString() + " VARIABLE";
        }
        return super.getHumanReadableImage();
    }

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";
        return "\n*OpDeclNode: " + this.getName() + "  " + super.toString(depth)
                + "\n  originallyDefinedInModule: " +
                (originallyDefinedInModule != null
                        ? originallyDefinedInModule.getName().toString()
                        : "<null>");
    }


    @Override
    protected String getNodeRef() {
        return "OpDeclNodeRef";
    }

    @Override
    protected Element getSymbolElement(final Document doc, final SymbolContext context) {
        final Element e = doc.createElement("OpDeclNode");
        e.appendChild(appendText(doc, "uniquename", getName().toString()));
        e.appendChild(appendText(doc, "arity", Integer.toString(getArity())));
        e.appendChild(appendText(doc, "kind", Integer.toString(getKind())));
        return e;
    }
}
