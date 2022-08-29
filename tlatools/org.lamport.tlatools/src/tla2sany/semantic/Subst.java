// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;
import tla2sany.xml.XMLExportable;
import tlc2.tool.coverage.CostModel;

import java.util.HashSet;
import java.util.Hashtable;

public class Subst implements LevelConstants, ASTConstants, ExploreNode, XMLExportable /* interface for exporting into XML */ {

    /**
     * This class represents a single substitution of the form
     * op <- expr such as appears in module instantiations.
     */
    private OpDeclNode op;
    private ExprOrOpArgNode expr;
    private TreeNode exprSTN;
    private boolean implicit;
    private CostModel cm = CostModel.DO_NOT_RECORD;

    /* Constructors */
    public Subst(final OpDeclNode odn, final ExprOrOpArgNode exp, final TreeNode exSTN, final boolean imp) {
        this.op = odn;
        this.expr = exp;
        this.exprSTN = exSTN;
        this.implicit = imp;
    }

    public static ExprOrOpArgNode getSub(final Object param, final Subst[] subs) {
        for (final Subst sub : subs) {
            if (sub.getOp() == param) {
                return sub.getExpr();
            }
        }
        return null;
    }

    public static HashSet<SymbolNode> paramSet(final SymbolNode param, final Subst[] subs) {
        /***********************************************************************
         * If subs[i] is of the form `parm <- expr', then it returns the        *
         * expr.levelParams.  Otherwise, it returns the HashSet containing      *
         * only param.                                                          *
         *                                                                      *
         * This should only be called after level checking has been called on   *
         * all subs[i].getExpr().                                               *
         ***********************************************************************/
        int idx;
        for (idx = 0; idx < subs.length; idx++) {
            if (subs[idx].getOp() == param) break;
        }
        if (idx < subs.length) {
            return subs[idx].getExpr().getLevelParams();
        }

        final HashSet<SymbolNode> res = new HashSet<>();
        res.add(param);
        return res;
    }

    public static HashSet<SymbolNode> allParamSet(final SymbolNode param, final Subst[] subs) {
        /***********************************************************************
         * This is exactly like paramSet, except it returns the allParams       *
         * HashSet instead of levelParams.                                      *
         ***********************************************************************/
        int idx;
        for (idx = 0; idx < subs.length; idx++) {
            if (subs[idx].getOp() == param) break;
        }
        if (idx < subs.length) {
            return subs[idx].getExpr().getAllParams();
        }

        final HashSet<SymbolNode> res = new HashSet<>();
        res.add(param);
        return res;
    }

    public static SetOfLevelConstraints getSubLCSet(final LevelNode body,
                                                    final Subst[] subs,
                                                    final boolean isConstant,
                                                    final int itr) {
        /***********************************************************************
         * This should only be called after level checking has been called on   *
         * body and on all subs[i].getExpr().  The itr argument is the          *
         * iteration number for calling levelCheck.                             *
         ***********************************************************************/
        final SetOfLevelConstraints res = new SetOfLevelConstraints();
        final SetOfLevelConstraints lcSet = body.getLevelConstraints();
        for (final var kv : lcSet.entrySet()) {
            var param = kv.getKey();
            Integer plevel = kv.getValue();
            if (!isConstant) {
                if (param.getKind() == ConstantDeclKind) {
                    plevel = Levels[ConstantLevel];
                } else if (param.getKind() == VariableDeclKind) {
                    plevel = Levels[VariableLevel];
                }
            }
            for (final SymbolNode symbolNode : paramSet(param, subs)) {
                res.put(symbolNode, plevel);
            }
        }
        final HashSet<ArgLevelParam> alpSet = body.getArgLevelParams();
        /*****************************************************************
         * The call of getMaxLevel should be made only to a node that     *
         * has been level checked.  But this node has come from looking   *
         * up an operator in some hash table, and there's no way of       *
         * knowing if it's been level checked.  So, we have to level      *
         * check it first, which is why we need the iteration number      *
         * argument of this method.                                       *
         *****************************************************************/
        for (final ArgLevelParam alp : alpSet) {
            final OpArgNode sub = (OpArgNode) getSub(alp.op, subs);
            if (sub != null &&
                    sub.getOp() instanceof final OpDefNode subDef) {
                subDef.levelCheck(itr);
                /*****************************************************************
                 * The call of getMaxLevel should be made only to a node that     *
                 * has been level checked.  But this node has come from looking   *
                 * up an operator in some hash table, and there's no way of       *
                 * knowing if it's been level checked.  So, we have to level      *
                 * check it first, which is why we need the iteration number      *
                 * argument of this method.                                       *
                 *****************************************************************/
                final Integer mlevel = subDef.getMaxLevel(alp.i);
                for (final SymbolNode symbolNode : paramSet(alp.param, subs)) {
                    res.put(symbolNode, mlevel);
                }
            }
        }
        return res;
    }

    public static SetOfArgLevelConstraints getSubALCSet(
            final LevelNode body, final Subst[] subs, final int itr) {
        /***********************************************************************
         * Can be called only after levelCheck has been called on body.  The    *
         * argument itr is the argument for calling levelCheck.                 *
         ***********************************************************************/
        final SetOfArgLevelConstraints res = new SetOfArgLevelConstraints();
        final SetOfArgLevelConstraints alcSet = body.getArgLevelConstraints();
        for (var kv : alcSet.entrySet()) {
            var pap = kv.getKey();
            final Integer plevel = kv.getValue();
            final ExprOrOpArgNode sub = getSub(pap.param, subs);
            if (sub == null) {
                res.put(pap, plevel);
            } else {
                final SymbolNode subOp = ((OpArgNode) sub).getOp();
                if (subOp.isParam()) {
                    pap = new ParamAndPosition(subOp, pap.position);
                    res.put(pap, plevel);
                }
            }
        }
        final HashSet<ArgLevelParam> alpSet = body.getArgLevelParams();
        /***************************************************************
         * Must invoke levelCheck before invoking getLevel              *
         ***************************************************************/
        for (final ArgLevelParam alp : alpSet) {
            final ExprOrOpArgNode subParam = getSub(alp.param, subs);
            if (subParam != null) {
                final ExprOrOpArgNode subOp = getSub(alp.op, subs);
                final SymbolNode op = (subOp == null) ? alp.op : ((OpArgNode) subOp).getOp();
                if (op.isParam()) {
                    final ParamAndPosition pap = new ParamAndPosition(op, alp.i);
                    subParam.levelCheck(itr);
                    /***************************************************************
                     * Must invoke levelCheck before invoking getLevel              *
                     ***************************************************************/
                    final Integer subLevel = subParam.getLevel();
                    res.put(pap, subLevel);
                }
            }
        }
        return res;
    }

    public static HashSet<ArgLevelParam> getSubALPSet(final LevelNode body, final Subst[] subs) {
        /***********************************************************************
         * This should only be called after level checking has been called on   *
         * body and on all subs[i].getExpr().                                   *
         ***********************************************************************/
        final HashSet<ArgLevelParam> res = new HashSet<>();
        final HashSet<ArgLevelParam> alpSet = body.getArgLevelParams();
        for (final ArgLevelParam alp : alpSet) {
            final ExprOrOpArgNode sub = getSub(alp.op, subs);
            if (sub == null) {
                res.add(alp);
            } else {
                final SymbolNode subOp = ((OpArgNode) sub).getOp();
                if (subOp.isParam()) {
                    for (final SymbolNode symbolNode : paramSet(alp.param, subs)) {
                        res.add(new ArgLevelParam(subOp, alp.i, symbolNode));
                    }
                }
            }
        }
        return res;
    }

    public final OpDeclNode getOp() {
        return this.op;
    }

    public final void setOp(final OpDeclNode opd) {
        this.op = opd;
    }

    public final ExprOrOpArgNode getExpr() {
        return this.expr;
    }

    public final void setExpr(final ExprOrOpArgNode exp, final boolean imp) {
        this.expr = exp;
        this.implicit = imp;
    }

    public final TreeNode getExprSTN() {
        return this.exprSTN;
    }

    public final void setExprSTN(final TreeNode stn) {
        this.exprSTN = stn;
    }

    public final boolean isImplicit() {
        return this.implicit;
    }

    public final CostModel getCM() {
        return this.cm;
    }

    public final Subst setCM(final CostModel cm) {
        this.cm = cm;
        return this;
    }

    @Override
    public final String levelDataToString() {
        return "Dummy level string";
    }

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        visitor.preVisit(this);
        if (op != null) op.walkGraph(semNodesTable, visitor);
        if (expr != null) expr.walkGraph(semNodesTable, visitor);
        visitor.postVisit(this);
    }

    @Override
    public final String toString(final int depth) {
        return "\nOp: " + Strings.indent(2, (op != null ? op.toString(depth - 1) :
                "<null>")) +
                "\nExpr: " + Strings.indent(2, (expr != null ? expr.toString(depth - 1) : "<null>"));
    }

    @Override
    public Element export(final Document doc, final SymbolContext context) {
        final Element ret = doc.createElement("Subst");
        ret.appendChild(op.export(doc, context));
        ret.appendChild(expr.export(doc, context));
        return ret;
    }

}
