// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import util.UniqueString;

public class InstanceNode extends LevelNode {

  /**
   * This class represents a TLA module instantiation whose general form is
   *
   *    I(param[1], ... , param[p]) ==                                    
   *       INSTANCE M WITH mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]
   *
   * or simply
   *
   *   INSTANCE M WITH mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]
   * 
   *  where I         instance name
   *        param[i]  instance paramater
   *        M         module being instantiated
   *        mparam[i] constant and variable declared in M
   *        mexp[i]   expression substituted for mexp[i] in this instance
   *
   *  The parameters param[1] ... params[p] may be missing if there
   *  are no instance params; the name I (and the "==") may also be
   *  missing if this is an unnamed instance.  The substitutions WITH
   *  mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r] may be missing if
   *  module M does not declare any constants or variables; and any
   *  particular substitution mparam[i] <- mexp[i] if the expression
   *  mexp[i] is a simply a reference to a constant or variable
   *  declared in the current module that has the same name as mparam[i]
   *  declared in M (or a module M extends).
   *  
   *  On 30 Jan 2013, LL added some public get...() methods that
   *  return some fields.
   */      

  UniqueString      name;     
     // The name of this instance, e.g. "I" in the example above;
     //   null if this is an unnamed instance.
  
  public UniqueString getName() {
      return name ;
  }
  FormalParamNode[] params;   
     // The instance parameters, e.g. param[1]  ... param[n] in the
     // example above. Has length zero if there is no param.
  ModuleNode        module;   
     // Reference to the module, M, being instantiated
  
  public ModuleNode getModule() {
      return module ;
  }
  
  Subst[]           substs;   
     // The substitutions mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]
     // This includes substitutions not explicitly mentioned in the
     // surface syntax because they are of the form c <- c or x <- x
     // Have length 0 if there is no substitution.

  
  /*************************************************************************
  * The following field was added by LL on 29 Jul 2007.                    *
  *************************************************************************/
  boolean local;
    /***********************************************************************
    * True iff this is a LOCAL instance.                                   *
    ***********************************************************************/

  public boolean getLocal() {
      return this.local ;
  }
 
  /**
   * If the InstanceNode is a proof step, this is the step number.  It
   * is made a UniqueString for consistency; there's no need to make
   * comparison efficient.  It is null if the proof step has only
   * a level (like <9>) rather than a complete step number.
   * Added by LL on 6 June 2010.
   */
  private UniqueString stepName = null;
  public void setStepName(UniqueString stepName)
   {
    this.stepName = stepName;
   }

  /**
   * @return the stepName
   */
  public UniqueString getStepName()
   {
    return stepName;
   }

  public InstanceNode(UniqueString name, boolean localness,
                      FormalParamNode[] params,
                      ModuleNode module, Subst[] substs, TreeNode stn) {
    super(InstanceKind, stn);
    this.name = name;
    this.local = localness;
    this.params = (params != null ? params : new FormalParamNode[0]);
    this.module = module;
    this.substs = (substs != null ? substs : new Subst[0]);
  }

  public boolean isLocal() { return local ; } 

  /* Level checking */
// These fields are now declared in all LevelNode subclasses
//  private boolean levelCorrect;
//  private SetOfLevelConstraints levelConstraints;
//  private SetOfArgLevelConstraints argLevelConstraints;
//  private HashSet argLevelParams;
  
  public final boolean levelCheck(int itr) {
    /***********************************************************************
    * I believe this should only be called once, with itr = 1.            *
    ***********************************************************************/
    if (this.levelChecked >= itr) return this.levelCorrect ;
    levelChecked = itr ;
    

    levelParams = new HashSet() ;
      /*********************************************************************
      * Added in SANY2.                                                    *
      *********************************************************************/
      
    /***********************************************************************
    * Level check the components this.module and this.substs[i].getExpr(). *
    ***********************************************************************/
    this.levelCorrect = true;
    if (!this.module.levelCheck(itr)) {
      this.levelCorrect = false;
    }
    for (int i = 0; i < this.substs.length; i++ ) {
      if (!this.substs[i].getExpr().levelCheck(itr)) {
        this.levelCorrect = false;
      }
    }

    // Check constraints on the substitution.
    for (int i = 0; i < this.substs.length; i++ ) {
      SymbolNode mparam = substs[i].getOp();
      ExprOrOpArgNode mexp = substs[i].getExpr();     
      mexp.levelCheck(itr) ;
      mparam.levelCheck(itr);
        /*****************************************************************
        * Have to call levelCheck on these objects before calling        *
        * getLevel.                                                      *
        *****************************************************************/
      /*********************************************************************
      * Check level constraints for a constant module.                     *
      *********************************************************************/
      if (!this.module.isConstant()) {
        if (mexp.getLevel() > mparam.getLevel()) {
          if (mexp.levelCheck(itr) && mparam.levelCheck(itr)) {
            errors.addError(
               this.stn.getLocation(), 
               "Level error in instantiating module '" + module.getName() +
               "':\nThe level of the expression or operator substituted for '" 
                   + mparam.getName() + 
               "' \nmust be at most " + mparam.getLevel() + ".");
          }
          this.levelCorrect = false;
         } //  if (mexp.getLevel() > mparam.getLevel()) 
       } // if (!this.module.isConstant())

        /*******************************************************************
        * For if mparam an operator parameter, check that mexp is          *
        * Leibniz.                                                         *
        *******************************************************************/
      if (mexp.getKind() == OpArgKind) {
        SymbolNode op = ((OpArgNode) mexp).getOp() ;
        if (   (   (op.getKind() == UserDefinedOpKind)
                || (op.getKind() == BuiltInKind))
            && ( ! ((OpDefNode) op).isLeibniz)) {
          errors.addError(
               this.stn.getLocation(), 
               "Error in instantiating module '" + module.getName() +
               "':\n A non-Leibniz operator substituted for '" 
                   + mparam.getName() + "'.");
            } // if ;
        } // if (mexp.getKind() == OpArgKind) ;
      } // for i

    SetOfLevelConstraints lcSet = this.module.getLevelConstraints();
    SetOfArgLevelConstraints alcSet = this.module.getArgLevelConstraints();    
    for (int i = 0; i < this.substs.length; i++ ) {
      SymbolNode mparam = substs[i].getOp();
      ExprOrOpArgNode mexp = substs[i].getExpr();
        /*******************************************************************
        * mexp was level-checked above.                                    *
        *******************************************************************/
      Integer plevel = (Integer)lcSet.get(mparam);
      if (plevel != null &&
          mexp.getLevel() > plevel.intValue()) {
        if (mexp.levelCheck(itr)) {
          errors.addError(this.stn.getLocation(), 
            "Level error in instantiating module '" + module.getName() +
            "':\nThe level of the expression or operator substituted for '" +
            mparam.getName() + "' \nmust be at most " + plevel + ".");
        }
        this.levelCorrect = false;
      }
      
      int alen = mparam.getArity();
      if (alen > 0 && ((OpArgNode)mexp).getOp() instanceof OpDefNode) {
        OpDefNode opDef = (OpDefNode)((OpArgNode)mexp).getOp();
        for (int j = 0; j < alen; j++) {
          ParamAndPosition pap = new ParamAndPosition(mparam, j);
          Integer alevel = (Integer)alcSet.get(pap);
          boolean opDefLevelCheck = opDef.levelCheck(itr) ;
            /***************************************************************
            * Need to call opDef.levelCheck before calling                 *
            * opDef.getMaxLevel.                                           *
            ***************************************************************/
          if (alevel != null &&
              opDef.getMaxLevel(j) < alevel.intValue()) {
            if (opDefLevelCheck) {
              /*************************************************************
              * Apparently, we only bother reporting this error if level   *
              * checking opDef didn't cause an error.                      *
              *************************************************************/
              errors.addError(
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

    Iterator iter = this.module.getArgLevelParams().iterator();
    while (iter.hasNext()) {
      ArgLevelParam alp = (ArgLevelParam)iter.next();
      for (int i = 0; i < this.substs.length; i++) {
        SymbolNode pi = this.substs[i].getOp();
        for (int j = 0; j < this.substs.length; j++) {
          if (alp.op == pi &&
              alp.param == this.substs[j].getOp()) {
            SymbolNode op = ((OpArgNode)this.substs[i].getExpr()).getOp();
            boolean opLevelCheck = op.levelCheck(itr) ;
               /************************************************************
               * Need to level check before calling op.getMaxLevel.        *
               ************************************************************/
            if (op instanceof OpDefNode && 
                this.substs[j].getExpr().getLevel() > 
                   ((OpDefNode)op).getMaxLevel(alp.i)) {
              if (opLevelCheck &&
                  this.substs[j].getExpr().levelCheck(itr)) {
                errors.addError(
                   this.stn.getLocation(), 
                   "Level error when instantiating module '" + 
                      module.getName() + "':\nThe level of the argument " + 
                      alp.i + " of the operator " +
                      pi.getName() + "' \nmust be at most " +
                      ((OpDefNode)op).getMaxLevel(alp.i) + ".");
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
    iter = lcSet.keySet().iterator();
    while (iter.hasNext()) {
      SymbolNode param = (SymbolNode)iter.next();
      if (!param.occur(this.params)) {
        this.levelConstraints.put(param, lcSet.get(param));
      }
    }
    for (int i = 0; i < this.substs.length; i++) {
      lcSet = this.substs[i].getExpr().getLevelConstraints();
      iter = lcSet.keySet().iterator();
      while (iter.hasNext()) {
        SymbolNode param = (SymbolNode)iter.next();
        if (!param.occur(this.params)) {
          this.levelConstraints.put(param, lcSet.get(param));
        }
      }
    }
    
//    this.argLevelConstraints = new SetOfArgLevelConstraints();
    alcSet = Subst.getSubALCSet(this.module, this.substs, itr);
    iter = alcSet.keySet().iterator();
    while (iter.hasNext()) {
      ParamAndPosition pap = (ParamAndPosition)iter.next();
      if (!pap.param.occur(this.params)) {
        this.argLevelConstraints.put(pap, alcSet.get(pap));
      }
    }
    for (int i = 0; i < this.substs.length; i++) {
      alcSet = this.substs[i].getExpr().getArgLevelConstraints();
      iter = alcSet.keySet().iterator();
      while (iter.hasNext()) {
        ParamAndPosition pap = (ParamAndPosition)iter.next();
        if (!pap.param.occur(this.params)) {
          this.argLevelConstraints.put(pap, alcSet.get(pap));
        }
      }
    }
    
//    this.argLevelParams = new HashSet();
    HashSet alpSet = Subst.getSubALPSet(this.module, this.substs);
      /*********************************************************************
      * At this point, levelCheck(itr) has been called on this.module      *
      * and all nodes substs[i].getExpr(), which is a precondition for     *
      * calling getSubALPSet.                                              *
      *********************************************************************/
    iter = alpSet.iterator();
    while (iter.hasNext()) {
      ArgLevelParam alp = (ArgLevelParam)iter.next();
      if (!alp.occur(this.params)) {
        this.argLevelParams.add(alp);
      }
    }
    for (int i = 0; i < this.substs.length; i++) {
      alpSet = this.substs[i].getExpr().getArgLevelParams();
      iter = alpSet.iterator();
      while (iter.hasNext()) {
        ArgLevelParam alp = (ArgLevelParam)iter.next();
        if (!alp.occur(this.params)) {
          this.argLevelParams.add(alp);
        }
      }
    }
    return this.levelCorrect;
  }

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

  public final HashSet getLevelParams() {
    /***********************************************************************
    * In SANY1, this was never called.  However, in SANY2 it is called     *
    * for instance nodes inside proofs.                                    *
    ***********************************************************************/
// Assert.fail("Internal Error: Should never call InstanceNode.getLevelParams().");
    return levelParams ; // make compiler happy
  }
  
  public final SetOfLevelConstraints getLevelConstraints() { 
    return this.levelConstraints;
  }

//  public final SetOfArgLevelConstraints getArgLevelConstraints() { 
//    return this.argLevelConstraints;
//  }
//  
//  public final HashSet getArgLevelParams() { return this.argLevelParams; }

  public final String levelDataToString() {
    return "LevelConstraints: "    + this.levelConstraints    + "\n" +
           "ArgLevelConstraints: " + this.argLevelConstraints + "\n" +
           "ArgLevelParams: "      + this.argLevelParams      + "\n";
  }
  /**
   * The children of an instance are the expressions beings
   * substituted for parameters.
   */
  public SemanticNode[] getChildren() {
      SemanticNode[] res = new SemanticNode[substs.length];
      for (int i = 0; i < substs.length; i++) {
          res[i] = substs[i].getExpr();
      }
      return res;
   }
  
  public final void walkGaph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;

    semNodesTable.put(new Integer(myUID), this);

    for (int i = 0; i < params.length; i++) {
      params[i].walkGraph(semNodesTable);
    }
    module.walkGraph(semNodesTable);
  }

  public final String toString(int depth) {
    if (depth <= 0) return "";

    String ret = "\n*InstanceNode " + super.toString(depth) + 
                 "  InstanceName = " + (name == null ? "(none)" : name.toString()) +
                 Strings.indent(2, "\nModule: " + module.getName())
   +             Strings.indent(2, "\nlocal: " + this.local);
    if (params.length > 0) {
      ret += Strings.indent(2,"\nInstance parameters:");
      for ( int i = 0; i < params.length; i++ ) {
        ret += Strings.indent(4,params[i].toString(depth-1));
      }
    }

    if (substs.length > 0) {
      ret += Strings.indent(2, "\nSubstitutions:");
      for (int i = 0; i < substs.length; i++) {
        ret += Strings.indent(2,
                              Strings.indent(2, "\nSubst:" +
                                             (substs[i] != null ?
                                              Strings.indent(2, substs[i].toString(depth-1)) :
                                              "<null>")));
      }
    }
    return ret;
  }

}
