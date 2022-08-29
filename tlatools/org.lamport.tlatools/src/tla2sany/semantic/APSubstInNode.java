// Portions Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
//
// last modified on Thu 29 Nov 2007 at 13:22:32 PST by lamport

/***************************************************************************
 * This is like a SubstInNode, except where the body is a LevelNode         *
 * instead of an ExprNode.  It is used for substitution in the body of a    *
 * ThmOrAssumpDefNode, which may be either an ExprNode or an                *
 * AssumeProveNode.                                                         *
 *                                                                          *
 * Similarly to a SubstInNode, an APSubstInNode can appear only as the      *
 * body of a ThmOrAssumpDefNode or as the body of an APSubstInNode.  This   *
 * invariant must be maintained or the handling of subexpression-naming     *
 * expressions will break.                                                  *
 ***************************************************************************/


package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;
import util.UniqueString;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

public class APSubstInNode extends LevelNode {
    // The expression that the substitutions apply to
    private final ModuleNode instantiatingModule;
    // The module doing the instantiating that resulted in
    //   THIS APSubstInNode
    private final ModuleNode instantiatedModule;
    /**
     * For a APSubstInNode object s that has the WITH clause
     * <p>
     * A <- x+1, B <- x*r
     * <p>
     * <p>
     * The substitutions can be accessed as follows:
     * <p>
     * s.getSubFor(0)  = a ref to the ConstantDecl or VariableDecl
     * node for A
     * s.getSubFor(1)  = a ref to the ConstantDecl or VariableDecl
     * node for B
     * s.getSubWith(0) = a ref to the ExprNode for x+1
     * s.getSubWith(1) = a ref to the ExprNode for x*r
     */
    private Subst[] substs;
    // List of explicit and implicit substitutions to be
    // applied to the body.  It should contain substitution
    // for all CONSTANTS and VARIABLES declared in the
    // module being instantiated (whether or not they appear
    // explicitly in the substitution list.
    private LevelNode body;
    // The module being instantiated

    public APSubstInNode(final TreeNode treeNode, final Subst[] subs, final LevelNode expr,
                         final ModuleNode ingmn, final ModuleNode edmn) {
        super(APSubstInKind, treeNode);
        this.substs = subs;
        this.body = expr;
        this.instantiatingModule = ingmn;
        this.instantiatedModule = edmn;
        if (this.body == null) {
            errors.get().addError(treeNode.getLocation(), "Substitution error, " +
                    "probably due to error in module being instantiated.");
        }
    }


    public final Subst[] getSubsts() {
        return this.substs;
    }

    public final LevelNode getBody() {
        return this.body;
    }

    public final void setBody(final LevelNode expr) {
        this.body = expr;
    }

    public final ModuleNode getInstantiatingModule() {
        return this.instantiatingModule;
    }

    public final ModuleNode getInstantiatedModule() {
        return this.instantiatedModule;
    }

    /**
     * Returns the OpDeclNode of the ith element of the substitution
     * list.
     */
    public final OpDeclNode getSubFor(final int i) {
        return this.substs[i].getOp();
    }

    /**
     * Returns the ExprOrOpArgNode of the ith element of the
     * substitution list.
     */
    public final ExprOrOpArgNode getSubWith(final int i) {
        return this.substs[i].getExpr();
    }

    /**
     * Add a substitution to the substitutions array, either by
     * overwriting a legal implicit substitution, if one matches, or
     * creating a new one.  In general, the substitutions array on entry
     * to this method can contain a mixture of explicit and implicit
     * substitutions
     */
    @SuppressWarnings("unused")    // TODO final else block is dead code
    final void addExplicitSubstitute(final Context instanceCtxt, final UniqueString lhs,
                                     final TreeNode stn, final ExprOrOpArgNode sub) {
        int index;
        for (index = 0; index < this.substs.length; index++) {
            if (lhs == this.substs[index].getOp().getName()) break;
        }

        if (index < this.substs.length) {
            if (!this.substs[index].isImplicit()) {
                // if it is not an implicit substitution, then replacing it is
                // an error.
                errors.get().addError(stn.getLocation(), "Multiple substitutions for symbol '" +
                        lhs.toString() + "' in substitution.");
            } else {
                // if it is an implicit subst, then replacing it with an
                // explicit one is fine.
                this.substs[index].setExpr(sub, false);
                this.substs[index].setExprSTN(stn);
            }
        } else {
            // but if it is not in the array of implicit substitutions, it
            // is probably because the lhs symbols is not known in the
            // instancer context, which is OK.  But it better be known in
            // the instancee context

            // look up the lhs symbol in the instancee context
            final SymbolNode lhsSymbol = instanceCtxt.getSymbol(lhs);

            // lhs must be an OpDeclNode; if not just return, as this error
            // will have been earlier, though semantic analysis was allowed
            // to continue.
            if (!(lhsSymbol instanceof OpDeclNode)) {
                return;
            }

            // if the symbol was found, then create a Subst node for it and
            // append it to the substitutions array (which requires a new
            // array allocation and full copy, unfortunately (should fix
            // this at some point)
            final int newlength = this.substs.length + 1;
            final Subst[] newSubsts = new Subst[newlength];
            final Subst newSubst = new Subst((OpDeclNode) lhsSymbol, sub, stn, false);

            System.arraycopy(this.substs, 0, newSubsts, 0, newlength - 1);
            newSubsts[newlength - 1] = newSubst;

            // replace the old array with the new one
            this.substs = newSubsts;
        }
    }

    /**
     * Make sure there is a substitution for every CONSTANT and VARIABLE
     * of an instantiated module.  If not, try the default, which is
     * that a CONSTANT or VARIABLE X not explicitly substituted for, is
     * implicitly subject to the substitution X <- X.  If that is not
     * possible, because X is not defined in the instantiating module,
     * then we have an error.
     */
    final void matchAll(final ArrayList<OpDeclNode> decls) {
        for (OpDeclNode decl : decls) {
            // Get the name of the i'th operator that must be substituted for
            final UniqueString opName = decl.getName();

            // See if it is represented in the substitutions array
            int j;
            for (j = 0; j < this.substs.length; j++) {
                if (this.substs[j].getOp().getName() == opName) break;
            }

            // If not, then report an error
            if (j >= this.substs.length) {
                errors.get().addError(stn.getLocation(),
                        "Substitution missing for symbol " + opName + " declared at " +
                                decl.getTreeNode().getLocation() +
                                " \nand instantiated in module " + instantiatingModule.getName() + ".");
            }
        }
    }

    /* Level check */
// These nodes are now part of all LevelNode subclasses.

    @Override
    public final boolean levelCheck(final int itr) {
        if (this.levelChecked >= itr) return this.levelCorrect;
        this.levelChecked = itr;

        /***********************************************************************
         * Level check the components body and substs.getSubWith(i) which       *
         * equals substs[i].getExpr().                                          *
         ***********************************************************************/
        this.levelCorrect = this.body.levelCheck(itr);
        for (int i = 0; i < this.substs.length; i++) {
            if (!this.getSubWith(i).levelCheck(itr)) {
                this.levelCorrect = false;
            }
        }

        // Calculate the level information
        this.level = this.body.getLevel();
        final HashSet<SymbolNode> lpSet = this.body.getLevelParams();
        for (int i = 0; i < this.substs.length; i++) {
            if (lpSet.contains(this.getSubFor(i))) {
                this.level = Math.max(level, this.getSubWith(i).getLevel());
            }
        }

        Iterator<SymbolNode> iter = lpSet.iterator();
        while (iter.hasNext()) {
            this.levelParams.addAll(Subst.paramSet(iter.next(), this.substs));
            /*******************************************************************
             * At this point, levelCheck(itr) has been invoked on              *
             * this.substs[i].getExpr() (which equals this.getSubWith(i)).      *
             *******************************************************************/
        }

        /***********************************************************************
         * For Leibniz checking, we now repeat everything done to compute       *
         * this.levelParams to compute this.allParams, except using             *
         * Subst.allParamSet instead of Subst.paramSet.                         *
         ***********************************************************************/
        final HashSet<SymbolNode> apSet = this.body.getAllParams();
        iter = apSet.iterator();
        while (iter.hasNext()) {
            this.allParams.addAll(Subst.allParamSet(iter.next(), this.substs));
            /*******************************************************************
             * At this point, levelCheck(itr) has been invoked on              *
             * this.substs[i].getExpr() (which equals this.getSubWith(i)).      *
             *******************************************************************/
        }

        final boolean isConstant = this.instantiatedModule.isConstant();
        /*********************************************************************
         * It is not necessary to invoke levelCheck before invoking           *
         * isConstant.                                                        *
         *********************************************************************/
        this.levelConstraints = Subst.getSubLCSet(this.body, this.substs,
                isConstant, itr);
        /*********************************************************************
         * levelCheck(itr) has been called on body and the                   *
         * substs[i].getExpr(), as required.                                  *
         *********************************************************************/
        this.argLevelConstraints =
                Subst.getSubALCSet(this.body, this.substs, itr);
        this.argLevelParams = Subst.getSubALPSet(this.body, this.substs);
        /*********************************************************************
         * levelCheck(itr) has been called on body and the                   *
         * substs[i].getExpr(), as required.                                  *
         *********************************************************************/

        return this.levelCorrect;
    }

    /**
     * toString, levelDataToString, & walkGraph methods to implement
     * ExploreNode interface
     */

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";

        final StringBuilder ret = new StringBuilder("\n*APSubstInNode: "
                + super.toString(depth)
                + "\n  instantiating module: " + instantiatingModule.getName()
                + ", instantiated module: " + instantiatedModule.getName()
                + Strings.indent(2, "\nSubstitutions:"));
        if (this.substs != null) {
            for (final Subst subst : this.substs) {
                ret.append(Strings.indent(2,
                        Strings.indent(2, "\nSubst:" +
                                (subst != null ?
                                        Strings.indent(2, subst.toString(depth - 1)) :
                                        "<null>"))));
            }
        } else {
            ret.append(Strings.indent(2, "<null>"));
        }
        ret.append(Strings.indent(2, "\nBody:"
                + Strings.indent(2, (body == null ? "<null>" : body.toString(depth - 1)))));
        return ret.toString();
    }

    /**
     * The children of this node are the body and the expressions
     * being substituted for symbols.
     */
    @Override
    public SemanticNode[] getChildren() {
        final SemanticNode[] res = new SemanticNode[this.substs.length + 1];
        res[0] = this.body;
        for (int i = 0; i < substs.length; i++) {
            res[i + 1] = substs[i].getExpr();
        }
        return res;
    }

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;
        if (semNodesTable.get(uid) != null) return;

        semNodesTable.put(uid, this);
        visitor.preVisit(this);

        if (this.substs != null) {
            for (final Subst subst : this.substs) {
                if (subst != null) subst.walkGraph(semNodesTable, visitor);
            }
        }
        if (this.body != null) this.body.walkGraph(semNodesTable, visitor);
        visitor.postVisit(this);
    }

    @Override
    protected Element getLevelElement(final Document doc, final SymbolContext context) {
        final Element sbts = doc.createElement("substs");
        for (final Subst subst : substs) {
            sbts.appendChild(subst.export(doc, context));
        }
        final Element bdy = doc.createElement("body");
        bdy.appendChild(body.export(doc, context));

        final Element from = doc.createElement("instFrom");
        final Element fromchild = this.instantiatingModule.export(doc, context);
        from.appendChild(fromchild);

        final Element to = doc.createElement("instTo");
        final Element tochild = instantiatedModule.export(doc, context);
        to.appendChild(tochild);


        final Element ret = doc.createElement("APSubstInNode");
        ret.appendChild(sbts);
        ret.appendChild(bdy);
        ret.appendChild(from);
        ret.appendChild(to);

        // at the end, we append the context of the symbols used in this node
        //ret.appendChild(context.export(doc));

        return ret;
    }
}
