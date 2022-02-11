// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// last modified on Mon 16 February 2009 at  9:57:46 PST by lamport 

package tla2sany.semantic;

import util.UniqueString;

public interface ASTConstants {

  /* The following are kinds of SemanticNodes. */
  public final int ModuleKind         = 1;  // Used for ModuleNodes
  public final int ConstantDeclKind   = 2;  
     // A kind of OpDeclNode; used for constants
  public final int VariableDeclKind   = 3;  
     // A kind of OpDeclNode; used for variables
  public final int BoundSymbolKind    = 4;  
    // A kind of OpDeclNode; used for symbols bound by quantifier-like ops
  public final int UserDefinedOpKind  = 5;  
     // A kind of OpDefNode; used for OpDefNodes for user-defined ops
  public final int ModuleInstanceKind = 6;  
     // A kind of OpDefNode; used for "M" in M(x) == INSTANCE Foo ...
  public final int BuiltInKind        = 7;  
    // A kind of OpDefNode; used only for OpDefNodes of built-in ops
  public static final int OpArgKind          = 8;
  public static final int OpApplKind         = 9;
  public static final int LetInKind          = 10;
  public static final int FormalParamKind    = 11;
  public static final int TheoremKind        = 12;
  public static final int SubstInKind        = 13;
  public static final int AssumeProveKind    = 14;
//  public static final int ProofKind          = 15;
  public static final int NumeralKind        = 16;
  public static final int DecimalKind        = 17;
  public static final int StringKind         = 18;
  public static final int AtNodeKind         = 19;
  public static final int AssumeKind         = 20;
  public static final int InstanceKind       = 21; 
    // Used for InstanceNodes, representing an INSTANCE stmt
    // or def (whether named or not). Not to be confused with
    // ModuleInstanceKind above, which represents a name that
    // must not be (re)used for a user-defined operator.
  public static final int NewSymbKind        = 22; 
    // Added by LL on 15 Mar 2007
  public static final int ThmOrAssumpDefKind = 23; 
    // Added by LL on 17 Mar 2007

  /*************************************************************************
  * The following are kinds of OpDeclNode used for a declaration in the    *
  * assumptions list of an AssumeProve.                                    *
  *                                                                        *
  * Added by LL on 22 Mar 2007                                             *
  *************************************************************************/
  public static final int NewConstantKind    = 24;
  public static final int NewVariableKind    = 25;
  public static final int NewStateKind       = 26;
  public static final int NewActionKind      = 27;
  public static final int NewTemporalKind    = 28;

  public static final int LabelKind          = 29; 
  public static final int APSubstInKind      = 30; 
  public static final int UseKind            = 31;
  public static final int HideKind           = 32;
  public static final int LeafProofKind      = 33;
  public static final int NonLeafProofKind   = 34;
  public static final int QEDStepKind        = 35;
  public static final int DefStepKind        = 36;
  public static final int NumberedProofStepKind = 37;


  /*************************************************************************
  * AN array of printable names for the constants defined above.           *
  *************************************************************************/
  public static final String[] kinds = {
    /*  0 */ null,
    /*  1 */ "ModuleKind",
    /*  2 */ "ConstantDeclKind",
    /*  3 */ "VariableDeclKind",
    /*  4 */ "BoundSymbolKind",
    /*  5 */ "UserDefinedOpKind",
    /*  6 */ "ModuleInstanceKind",
    /*  7 */ "BuiltInKind",
    /*  8 */ "OpArgKind",    
    /*  9 */ "OpApplKind",
    /* 10 */ "LetInKind",
    /* 11 */ "FormalParamKind",
    /* 12 */ "TheoremKind",
    /* 13 */ "SubstInKind",
    /* 14 */ "AssumeProveKind",
    /* 15 */ "ProofKind",
    /* 16 */ "NumeralKind",
    /* 17 */ "DecimalKind",
    /* 18 */ "StringKind",
    /* 19 */ "AtNodeKind",
    /* 20 */ "AssumeKind",
    /* 21 */ "InstanceKind",
    /* 22 */ "NewSymbKind",
    /* 23 */ "ThmOrAssumpDefKind",
    /* 24 */ "NewConstantKind",
    /* 25 */ "NewVariableKind",
    /* 26 */ "NewStateKind",
    /* 27 */ "NewActionKind",
    /* 28 */ "NewTemporalKind",
    /* 29 */ "LabelKind",
    /* 30 */ "APSubstInKind",
    /* 31 */ "UseKind",
    /* 32 */ "HideKind",
    /* 33 */ "LeafProofKind",
    /* 34 */ "NonLeafProofKind",
    /* 35 */ "QEDStepKind",
    /* 36 */ "DefStepKind",
    /* 37 */ "NumberedProofStepKind"
  };

  /* Operators */
  public static String OP_aa   = ("$AngleAct");
  public static String OP_bc   = ("$BoundedChoose");
  public static String OP_be   = ("$BoundedExists");
  public static String OP_bf   = ("$BoundedForall");
  public static String OP_case = ("$Case");
  public static String OP_cp   = ("$CartesianProd");
  public static String OP_cl   = ("$ConjList");
  public static String OP_dl   = ("$DisjList");
  public static String OP_exc  = ("$Except");
  public static String OP_fa   = ("$FcnApply");
  public static String OP_fc   = ("$FcnConstructor");
  public static String OP_ite  = ("$IfThenElse");
  public static String OP_nrfs = ("$NonRecursiveFcnSpec");
  public static String OP_pair = ("$Pair");
  public static String OP_rc   = ("$RcdConstructor");
  public static String OP_rs   = ("$RcdSelect");
  public static String OP_rfs  = ("$RecursiveFcnSpec");
  public static String OP_seq  = ("$Seq");
  public static String OP_sa   = ("$SquareAct");
  public static String OP_se   = ("$SetEnumerate");
  public static String OP_sf   = ("$SF");
  public static String OP_soa  = ("$SetOfAll");
  public static String OP_sor  = ("$SetOfRcds");
  public static String OP_sof  = ("$SetOfFcns");
  public static String OP_sso  = ("$SubsetOf");
  public static String OP_tup  = ("$Tuple");
  public static String OP_te   = ("$TemporalExists");
  public static String OP_tf   = ("$TemporalForall");
  public static String OP_uc   = ("$UnboundedChoose");
  public static String OP_ue   = ("$UnboundedExists");
  public static String OP_uf   = ("$UnboundedForall");
  public static String OP_wf   = ("$WF");

  /*************************************************************************
  * The following added by LL 2-3 Aug 2007.                                *
  *************************************************************************/
  public static String OP_nop     = ("$Nop");
  public static String OP_qed     = ("$Qed");
  public static String OP_pfcase  = ("$Pfcase");
  public static String OP_have    = ("$Have");
  public static String OP_take    = ("$Take");
  public static String OP_pick    = ("$Pick");
  public static String OP_witness = ("$Witness");

  /*************************************************************************
  * OP_suffices added by LL 16 Feb 2009.                                   *
  *************************************************************************/
  public static String OP_suffices  = ("$Suffices");
  
  /*************************************************************************
  * OP_prime added by LL 2 Dec 2012.                                       *
  *************************************************************************/
  public static String OP_prime  = ("'");

}
