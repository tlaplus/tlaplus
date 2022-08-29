// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
//
// Last modified on Mon 23 February 2009 at  9:58:00 PST by lamport

package tla2sany.semantic;

/***************************************************************************
 * A SubstInNode is created to represent the substitutions performed in     *
 * module instantiation.  It can appear only as the body of an OpDefNode,   *
 * or as the body of a SubstInNode.  This invariant must be maintained      *
 * else the handling of expressions that represent subexpressions will      *
 * break.                                                                   *
 *                                                                          *
 * Note: The SubstInNode that represents a substitution A <- expA, B <-     *
 * expB with body Bod is at least almost equivalent to an OpApplNode whose  *
 * operator is LAMBDA A, B : Bod and whose arguments are expA and expB.     *
 * However, for reasons having to do with operators like ENABLED, in which  *
 * substitution in definitions isn't equivalent to logical substitution,    *
 * we can't handle them the way Lambda expressions are handled, by          *
 * creating new OpDef nodes.                                                *
 ***************************************************************************/

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

public class SubstInNode extends ExprNode {
    // The expression that the substitutions apply to
    private final ModuleNode instantiatingModule;
    // The module doing the instantiating that resulted in
    //   THIS SubstInNode
    private final ModuleNode instantiatedModule;
    /**
     * For a SubstInNode object s that has the WITH clause
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
    private ExprNode body;
    // The module being instantiated

    public SubstInNode(final TreeNode treeNode, final Subst[] subs, final ExprNode expr,
                       final ModuleNode ingmn, final ModuleNode edmn) {
        super(SubstInKind, treeNode);
        this.substs = subs;
        this.body = expr;
        this.instantiatingModule = ingmn;
        this.instantiatedModule = edmn;
        if (this.body == null) {
            errors.get().addError(treeNode.getLocation(), "Substitution error, " +
                    "probably due to error \nin module being instantiated.");
        }
    }

    /**
     * Special constructor for use when an array of default
     * substitutions is to be produced.
     */
    public SubstInNode(final TreeNode treeNode, final SymbolTable instancerST,
                       final ArrayList<OpDeclNode> instanceeDecls, final ModuleNode ingmn, final ModuleNode edmn, final Context context)
            throws AbortException {
        super(SubstInKind, treeNode);
        this.instantiatingModule = ingmn;
        this.instantiatedModule = edmn;
        constructSubst(instanceeDecls, instancerST, treeNode, context);
        this.body = null;
    }

    public final Subst[] getSubsts() {
        return this.substs;
    }

    public final ExprNode getBody() {
        return this.body;
    }

    public final void setBody(final ExprNode expr) {
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
     * For each element of the ArrayList of instanceeDecls of OpDeclNode's,
     * this method puts a default Subst for the same name into
     * "substitutions" if and only if the name can be resolved in the
     * instancerST, i.e.  the SymbolTable of the module doing the
     * instancing.
     * <p>
     * Fill the substitutions array with dummy substitutions, i.e. an
     * OpApplNode or an OpArgNode substituted for each CONSTANT of
     * VARIABLE OpDeclNode in ArrayList v.
     */
    final void constructSubst(final ArrayList<OpDeclNode> instanceeDecls, final SymbolTable instancerST,
                              final TreeNode treeNode, final Context context)
            throws AbortException {
        final ArrayList<Subst> vtemp = new ArrayList<>();

        // for each CONSTANT or VARIABLE declared in module being
        // instantiated (the instancee)
        for (final OpDeclNode decl : instanceeDecls) {
            // Get the OpDeclNode for the CONSTANT or VARIABLE being
            // substituted for, i.e. "c" in" c <- e"
            // Try to resolve the name in the instancer module so we can see
            // if it is recognized as an operator, and if so, what kind of
            // operator it is
            final SymbolNode symb = instancerST.resolveSymbol(decl.getName());

            // if the name could be resolved in the instancer module
            // (including parameters created on the LHS of the module
            // instance definition), then create a default substitution for
            // it.  If it cannot be resolved in instancerST, then do
            // nothing, because explicit substitutions have yet to be
            // processed, and then a check for completeness of the
            // substitutions will occur after that.
            if (symb != null) {
                // If "decl" is either a VARIABLE declaration, or a CONSTANT
                // declaration for an operator with no arguments, then the
                // expression being substituted must be an ExprNode.  But
                // otherwise (i.e. if it is a CONSTANT declaration for an
                // operator of at least one argument) then the expression being
                // substituted must be an OpArgNode. No other choices are legal.
                if (decl.getKind() == VariableDeclKind ||
                        (decl.getKind() == ConstantDeclKind &&
                                decl.getArity() == 0)) {
                    // Create a new Subst for c <- c, where the c on the RHS is
                    // an OpApplNode with zero arguments
                    vtemp.add(
                            new Subst(decl,
                                    new OpApplNode(symb, new ExprOrOpArgNode[0], treeNode, instantiatingModule, context),
                                    null, true));
                } else {
                    // Create a new Subst for c <- c, where the c on the RHS is an OpArgNode
                    vtemp.add(
                            new Subst(decl,
                                    new OpArgNode(symb, treeNode, instantiatingModule),
                                    null, true));
                } // end else
            } // end if
        } // end for

        // The ArrayList vtemp now contains all the default substitutions
        // that are legally possible. Make an array out of them
        this.substs = new Subst[vtemp.size()];
        for (int i = 0; i < vtemp.size(); i++) {
            this.substs[i] = vtemp.get(i);
        }
    } // end constructSubst()

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
    @SuppressWarnings("unchecked")
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

//    this.levelParams = new HashSet();
        /*******************************************************************
         * At this point, levelCheck(itr) has been invoked on              *
         * this.substs[i].getExpr() (which equals this.getSubWith(i)).      *
         *******************************************************************/
        for (final SymbolNode symbolNode : lpSet) {
            this.levelParams.addAll(Subst.paramSet(symbolNode, this.substs));
            /*******************************************************************
             * At this point, levelCheck(itr) has been invoked on              *
             * this.substs[i].getExpr() (which equals this.getSubWith(i)).      *
             *******************************************************************/
        }

        /***********************************************************************
         * The following code was added 22 May 2008 by LL. I had apparently     *
         * forgotten to add the code computing nonLeibnizParams and the         *
         * original code computed only allParams.                               *
         *                                                                      *
         * For Leibniz checking, we go through all the substitutions param <-   *
         * expr.  For each one, if param is in this.body.allParams, then we     *
         * add all parameters expr.allParams to this.allParams.  If param is    *
         * also in this.body.nonLeibnizParams, then we also add all those       *
         * parameters to this.nonLeibnizParams.                                 *
         ***********************************************************************/
// XXXXX Here's the bug.  Need to clone these HashSets, not just
//       set a ref to them.
// Same bug seems to appear in LetInNode with levelParams & allParams
//    (but may not be a bug)
// To check: in APSubstInNode: this.argLevelParams = Subst...
//           in OpDefNode: this.levelParams = EmptySet, ...
//            also, make sure everything set to EmptySet, EmptyLC, EmptyALC
//                  is not changed.

        /***********************************************************************
         * 23 February 2009: Added ".clone" to the following statements to fix  *
         * bug.                                                                 *
         ***********************************************************************/
        this.allParams = (HashSet<SymbolNode>) this.body.getAllParams().clone();
        this.nonLeibnizParams = (HashSet<SymbolNode>) this.body.getNonLeibnizParams().clone();
        /*******************************************************************
         * Remove param from this.allParams, add the substituting           *
         * expression's allParams to it, and add the substituting           *
         * expression's nonLeibnizParams to this.nonLeibnizParams.          *
         *******************************************************************/
        /*******************************************************************
         * If param is in this.body.nonLeibnizParams, remove it from        *
         * this.nonLeibnizParams and add the substituting expression's      *
         * allParams to it.                                                 *
         *******************************************************************/
        for (final Subst subst : this.substs) {
            final OpDeclNode param = subst.getOp();
            if (this.allParams.contains(param)) {
                /*******************************************************************
                 * Remove param from this.allParams, add the substituting           *
                 * expression's allParams to it, and add the substituting           *
                 * expression's nonLeibnizParams to this.nonLeibnizParams.          *
                 *******************************************************************/
                this.allParams.remove(param);
                this.allParams.addAll(subst.getExpr().getAllParams());
                this.nonLeibnizParams.addAll(
                        subst.getExpr().getNonLeibnizParams());

                /*******************************************************************
                 * If param is in this.body.nonLeibnizParams, remove it from        *
                 * this.nonLeibnizParams and add the substituting expression's      *
                 * allParams to it.                                                 *
                 *******************************************************************/
                if (this.nonLeibnizParams.contains(param)) {
                    this.nonLeibnizParams.remove(param);
                    this.nonLeibnizParams.addAll(subst.getExpr().getAllParams());

                }// if
            }// if (bodyParams.contains(param))
        }// for


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

        final StringBuilder ret = new StringBuilder("\n*SubstInNode: "
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

        final Element ret = doc.createElement("SubstInNode");
        ret.appendChild(sbts);
        ret.appendChild(bdy);
        ret.appendChild(from);
        ret.appendChild(to);
        // at the end, we append the context of the symbols used in this node
        //ret.appendChild(instanceeCtxt.export(doc));

        return ret;
    }
}





