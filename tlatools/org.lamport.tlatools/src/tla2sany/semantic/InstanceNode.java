// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import util.UniqueString;

import java.util.HashSet;

public class InstanceNode extends LevelNode {

    /**
     * This class represents a TLA module instantiation whose general form is
     * <p>
     * I(param[1], ... , param[p]) ==
     * INSTANCE M WITH mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]
     * <p>
     * or simply
     * <p>
     * INSTANCE M WITH mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]
     * <p>
     * where I         instance name
     * param[i]  instance paramater
     * M         module being instantiated
     * mparam[i] constant and variable declared in M
     * mexp[i]   expression substituted for mexp[i] in this instance
     * <p>
     * The parameters param[1] ... params[p] may be missing if there
     * are no instance params; the name I (and the "==") may also be
     * missing if this is an unnamed instance.  The substitutions WITH
     * mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r] may be missing if
     * module M does not declare any constants or variables; and any
     * particular substitution mparam[i] <- mexp[i] if the expression
     * mexp[i] is a simply a reference to a constant or variable
     * declared in the current module that has the same name as mparam[i]
     * declared in M (or a module M extends).
     * <p>
     * On 30 Jan 2013, LL added some public get...() methods that
     * return some fields.
     */

    final UniqueString name;
    // The name of this instance, e.g. "I" in the example above;
    //   null if this is an unnamed instance.
    final FormalParamNode[] params;
    // The instance parameters, e.g. param[1]  ... param[n] in the
    // example above. Has length zero if there is no param.
    final ModuleNode module;
    final Subst[] substs;
    // Reference to the module, M, being instantiated
    /*************************************************************************
     * The following field was added by LL on 29 Jul 2007.                    *
     *************************************************************************/
    final boolean local;
    /**
     * If the InstanceNode is a proof step, this is the step number.  It
     * is made a UniqueString for consistency; there's no need to make
     * comparison efficient.  It is null if the proof step has only
     * a level (like <9>) rather than a complete step number.
     * Added by LL on 6 June 2010.
     */
    private UniqueString stepName = null;
    // The substitutions mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]
    // This includes substitutions not explicitly mentioned in the
    // surface syntax because they are of the form c <- c or x <- x
    // Have length 0 if there is no substitution.


    public InstanceNode(final UniqueString name, final boolean localness,
                        final FormalParamNode[] params,
                        final ModuleNode module, final Subst[] substs, final TreeNode stn) {
        super(InstanceKind, stn);
        this.name = name;
        this.local = localness;
        this.params = (params != null ? params : new FormalParamNode[0]);
        this.module = module;
        this.substs = (substs != null ? substs : new Subst[0]);
    }

    public UniqueString getName() {
        return name;
    }

    public ModuleNode getModule() {
        return module;
    }

    /***********************************************************************
     * True iff this is a LOCAL instance.                                   *
     ***********************************************************************/

    public boolean getLocal() {
        return this.local;
    }

    /**
     * @return the stepName
     */
    public UniqueString getStepName() {
        return stepName;
    }

    public void setStepName(final UniqueString stepName) {
        this.stepName = stepName;
    }

    public boolean isLocal() {
        return local;
    }

    /* Level checking */
// These fields are now declared in all LevelNode subclasses

    @Override
    public final boolean levelCheck(final int itr) {
        /***********************************************************************
         * I believe this should only be called once, with itr = 1.            *
         ***********************************************************************/
        if (this.levelChecked >= itr) return this.levelCorrect;
        levelChecked = itr;


        levelParams = new HashSet<>();
        /*********************************************************************
         * Added in SANY2.                                                    *
         *********************************************************************/

        /***********************************************************************
         * Level check the components this.module and this.substs[i].getExpr(). *
         ***********************************************************************/
        this.levelCorrect = this.module.levelCheck(itr);
        for (final Subst subst2 : this.substs) {
            if (!subst2.getExpr().levelCheck(itr)) {
                this.levelCorrect = false;
            }
        }

        // Check constraints on the substitution.
        /*****************************************************************
         * Have to call levelCheck on these objects before calling        *
         * getLevel.                                                      *
         *****************************************************************/
        /*********************************************************************
         * Check level constraints for a constant module.                     *
         *********************************************************************/
        /*******************************************************************
         * For if mparam an operator parameter, check that mexp is          *
         * Leibniz.                                                         *
         *******************************************************************/
        for (final Subst subst1 : this.substs) {
            final SymbolNode mparam = subst1.getOp();
            final ExprOrOpArgNode mexp = subst1.getExpr();
            mexp.levelCheck(itr);
            mparam.levelCheck(itr);
            /*****************************************************************
             * Have to call levelCheck on these objects before calling        *
             * getLevel.                                                      *
             *****************************************************************/
            /*********************************************************************
             * Check level constraints for a constant module.                     *
             *********************************************************************/
            if (!this.module.isConstant() && mexp.getLevel() > mparam.getLevel()) {

                if (mexp.levelCheck(itr) && mparam.levelCheck(itr)) {
                    errors.get().addError(
                            this.stn.getLocation(),
                            "Level error in instantiating module '" + module.getName() +
                                    "':\nThe level of the expression or operator substituted for '"
                                    + mparam.getName() +
                                    "' \nmust be at most " + mparam.getLevel() + ".");
                }
                this.levelCorrect = false;
                //  if (mexp.getLevel() > mparam.getLevel())
            } // if (!this.module.isConstant())

            /*******************************************************************
             * For if mparam an operator parameter, check that mexp is          *
             * Leibniz.                                                         *
             *******************************************************************/
            if (mexp.getKind() == OpArgKind) {
                final SymbolNode op = ((OpArgNode) mexp).getOp();
                if (((op.getKind() == UserDefinedOpKind)
                        || (op.getKind() == BuiltInKind))
                        && (!((OpDefNode) op).isLeibniz)) {
                    errors.get().addError(
                            this.stn.getLocation(),
                            "Error in instantiating module '" + module.getName() +
                                    "':\n A non-Leibniz operator substituted for '"
                                    + mparam.getName() + "'.");
                } // if ;
            } // if (mexp.getKind() == OpArgKind) ;
        } // for i

        SetOfLevelConstraints lcSet = this.module.getLevelConstraints();
        SetOfArgLevelConstraints alcSet = this.module.getArgLevelConstraints();
        /*******************************************************************
         * mexp was level-checked above.                                    *
         *******************************************************************/
        /***************************************************************
         * Need to call opDef.levelCheck before calling                 *
         * opDef.getMaxLevel.                                           *
         ***************************************************************/
        /*************************************************************
         * Apparently, we only bother reporting this error if level   *
         * checking opDef didn't cause an error.                      *
         *************************************************************/
        for (final Subst element : this.substs) {
            final SymbolNode mparam = element.getOp();
            final ExprOrOpArgNode mexp = element.getExpr();
            /*******************************************************************
             * mexp was level-checked above.                                    *
             *******************************************************************/
            final Integer plevel = lcSet.get(mparam);
            if (plevel != null &&
                    mexp.getLevel() > plevel) {
                if (mexp.levelCheck(itr)) {
                    errors.get().addError(this.stn.getLocation(),
                            "Level error in instantiating module '" + module.getName() +
                                    "':\nThe level of the expression or operator substituted for '" +
                                    mparam.getName() + "' \nmust be at most " + plevel + ".");
                }
                this.levelCorrect = false;
            }

            final int alen = mparam.getArity();
            if (alen > 0 && ((OpArgNode) mexp).getOp() instanceof final OpDefNode opDef) {
                for (int j = 0; j < alen; j++) {
                    final ParamAndPosition pap = new ParamAndPosition(mparam, j);
                    final Integer alevel = alcSet.get(pap);
                    final boolean opDefLevelCheck = opDef.levelCheck(itr);
                    /***************************************************************
                     * Need to call opDef.levelCheck before calling                 *
                     * opDef.getMaxLevel.                                           *
                     ***************************************************************/
                    if (alevel != null &&
                            opDef.getMaxLevel(j) < alevel) {
                        if (opDefLevelCheck) {
                            /*************************************************************
                             * Apparently, we only bother reporting this error if level   *
                             * checking opDef didn't cause an error.                      *
                             *************************************************************/
                            errors.get().addError(
                                    this.stn.getLocation(),
                                    "Level error in instantiating module '" + module.getName() +
                                            "':\nThe level of the argument " + j + " of the operator " +
                                            opDef.getName() + " \nmust be at least " + plevel + ".");
                        }
                        this.levelCorrect = false;
                    }
                }
            }
        }

        /************************************************************
         * Need to level check before calling op.getMaxLevel.        *
         ************************************************************/
        for (final ArgLevelParam alp : this.module.getArgLevelParams()) {
            /************************************************************
             * Need to level check before calling op.getMaxLevel.        *
             ************************************************************/
            /************************************************************
             * Need to level check before calling op.getMaxLevel.        *
             ************************************************************/
            for (final Subst value : this.substs) {
                final SymbolNode pi = value.getOp();
                /************************************************************
                 * Need to level check before calling op.getMaxLevel.        *
                 ************************************************************/
                for (final Subst subst : this.substs) {
                    if (alp.op == pi &&
                            alp.param == subst.getOp()) {
                        final SymbolNode op = ((OpArgNode) value.getExpr()).getOp();
                        final boolean opLevelCheck = op.levelCheck(itr);
                        /************************************************************
                         * Need to level check before calling op.getMaxLevel.        *
                         ************************************************************/
                        if (op instanceof OpDefNode odn &&
                                subst.getExpr().getLevel() >
                                        odn.getMaxLevel(alp.i)) {
                            if (opLevelCheck &&
                                    subst.getExpr().levelCheck(itr)) {
                                errors.get().addError(
                                        this.stn.getLocation(),
                                        "Level error when instantiating module '" +
                                                module.getName() + "':\nThe level of the argument " +
                                                alp.i + " of the operator " +
                                                pi.getName() + "' \nmust be at most " +
                                                odn.getMaxLevel(alp.i) + ".");
                            }
                            this.levelCorrect = false;
                        }
                    }
                } // for f
            } // for i
        } // while (iter.hasNext())

        // Calculate level information.
//    this.levelConstraints = new SetOfLevelConstraints();
        lcSet = Subst.getSubLCSet(this.module, this.substs,
                this.module.isConstant(), itr);
        /*********************************************************************
         * At this point, levelCheck(itr) has been called on this.module and  *
         * on all nodes substs[i].getExpr(), which is a precondition for      *
         * calling getSubLCSet.                                               *
         *********************************************************************/
        for (final SymbolNode param : lcSet.keySet()) {
            if (!param.occur(this.params)) {
                this.levelConstraints.put(param, lcSet.get(param));
            }
        }
        for (final Subst item : this.substs) {
            lcSet = item.getExpr().getLevelConstraints();
            for (final SymbolNode param : lcSet.keySet()) {
                if (!param.occur(this.params)) {
                    this.levelConstraints.put(param, lcSet.get(param));
                }
            }
        }

//    this.argLevelConstraints = new SetOfArgLevelConstraints();
        alcSet = Subst.getSubALCSet(this.module, this.substs, itr);
        for (final ParamAndPosition pap : alcSet.keySet()) {
            if (!pap.param.occur(this.params)) {
                this.argLevelConstraints.put(pap, alcSet.get(pap));
            }
        }
        for (final Subst value : this.substs) {
            alcSet = value.getExpr().getArgLevelConstraints();
            for (final ParamAndPosition pap : alcSet.keySet()) {
                if (!pap.param.occur(this.params)) {
                    this.argLevelConstraints.put(pap, alcSet.get(pap));
                }
            }
        }

//    this.argLevelParams = new HashSet();
        HashSet<ArgLevelParam> alpSet = Subst.getSubALPSet(this.module, this.substs);
        /*********************************************************************
         * At this point, levelCheck(itr) has been called on this.module      *
         * and all nodes substs[i].getExpr(), which is a precondition for     *
         * calling getSubALPSet.                                              *
         *********************************************************************/
        for (final ArgLevelParam alp : alpSet) {
            if (!alp.occur(this.params)) {
                this.argLevelParams.add(alp);
            }
        }
        for (final Subst subst : this.substs) {
            alpSet = subst.getExpr().getArgLevelParams();
            for (final ArgLevelParam alp : alpSet) {
                if (!alp.occur(this.params)) {
                    this.argLevelParams.add(alp);
                }
            }
        }
        return this.levelCorrect;
    }

    @Override
    public final int getLevel() {
        /***********************************************************************
         * In SANY1, this was never called.  In SANY2 it is called for          *
         * instance nodes inside proofs.  However, the INSTANCE doesn't affect  *
         * the proof's level because it only imports definitions, so we let     *
         * its level be 0.                                                      *
         ***********************************************************************/
// Assert.fail("Internal Error: Should never call InstanceNode.getLevel().");
        return 0;    // make compiler happy
    }

    @Override
    public final HashSet<SymbolNode> getLevelParams() {
        /***********************************************************************
         * In SANY1, this was never called.  However, in SANY2 it is called     *
         * for instance nodes inside proofs.                                    *
         ***********************************************************************/
// Assert.fail("Internal Error: Should never call InstanceNode.getLevelParams().");
        return levelParams; // make compiler happy
    }

    @Override
    public final SetOfLevelConstraints getLevelConstraints() {
        return this.levelConstraints;
    }

    @Override
    public final String levelDataToString() {
        return "LevelConstraints: " + this.levelConstraints + "\n" +
                "ArgLevelConstraints: " + this.argLevelConstraints + "\n" +
                "ArgLevelParams: " + this.argLevelParams + "\n";
    }

    /**
     * The children of an instance are the expressions beings
     * substituted for parameters.
     */
    @Override
    public SemanticNode[] getChildren() {
        final SemanticNode[] res = new SemanticNode[substs.length];
        for (int i = 0; i < substs.length; i++) {
            res[i] = substs[i].getExpr();
        }
        return res;
    }


    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";

        final StringBuilder ret = new StringBuilder("\n*InstanceNode " + super.toString(depth) +
                "  InstanceName = " + (name == null ? "(none)" : name.toString()) +
                Strings.indent(2, "\nModule: " + module.getName())
                + Strings.indent(2, "\nlocal: " + this.local));
        if (params.length > 0) {
            ret.append(Strings.indent(2, "\nInstance parameters:"));
            for (final FormalParamNode param : params) {
                ret.append(Strings.indent(4, param.toString(depth - 1)));
            }
        }

        if (substs.length > 0) {
            ret.append(Strings.indent(2, "\nSubstitutions:"));
            for (final Subst subst : substs) {
                ret.append(Strings.indent(2,
                        Strings.indent(2, "\nSubst:" +
                                (subst != null ?
                                        Strings.indent(2, subst.toString(depth - 1)) :
                                        "<null>"))));
            }
        }
        return ret.toString();
    }

    @Override
    protected Element getLevelElement(final Document doc, final tla2sany.xml.SymbolContext context) {

        final Element sbts = doc.createElement("substs");
        for (final Subst subst : substs) {
            sbts.appendChild(subst.export(doc, context));
        }

        final Element prms = doc.createElement("params");
        for (final FormalParamNode param : params) {
            prms.appendChild(param.export(doc, context));
        }

        final Element ret = doc.createElement("InstanceNode");
        if (name != null) ret.appendChild(appendText(doc, "uniquename", name.toString()));
        ret.appendChild(appendText(doc, "module", module.getName().toString()));
        ret.appendChild(sbts);
        ret.appendChild(prms);
        return ret;
    }

}
