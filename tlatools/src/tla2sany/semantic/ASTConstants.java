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
  public static UniqueString OP_aa   = UniqueString.uniqueStringOf("$AngleAct");
  public static UniqueString OP_bc   = UniqueString.uniqueStringOf("$BoundedChoose");
  public static UniqueString OP_be   = UniqueString.uniqueStringOf("$BoundedExists");
  public static UniqueString OP_bf   = UniqueString.uniqueStringOf("$BoundedForall");
  public static UniqueString OP_case = UniqueString.uniqueStringOf("$Case");
  public static UniqueString OP_cp   = UniqueString.uniqueStringOf("$CartesianProd");
  public static UniqueString OP_cl   = UniqueString.uniqueStringOf("$ConjList");
  public static UniqueString OP_dl   = UniqueString.uniqueStringOf("$DisjList");
  public static UniqueString OP_exc  = UniqueString.uniqueStringOf("$Except");
  public static UniqueString OP_fa   = UniqueString.uniqueStringOf("$FcnApply");
  public static UniqueString OP_fc   = UniqueString.uniqueStringOf("$FcnConstructor");
  public static UniqueString OP_ite  = UniqueString.uniqueStringOf("$IfThenElse");
  public static UniqueString OP_nrfs = UniqueString.uniqueStringOf("$NonRecursiveFcnSpec");
  public static UniqueString OP_pair = UniqueString.uniqueStringOf("$Pair");
  public static UniqueString OP_rc   = UniqueString.uniqueStringOf("$RcdConstructor");
  public static UniqueString OP_rs   = UniqueString.uniqueStringOf("$RcdSelect");
  public static UniqueString OP_rfs  = UniqueString.uniqueStringOf("$RecursiveFcnSpec");
  public static UniqueString OP_seq  = UniqueString.uniqueStringOf("$Seq");
  public static UniqueString OP_sa   = UniqueString.uniqueStringOf("$SquareAct");
  public static UniqueString OP_se   = UniqueString.uniqueStringOf("$SetEnumerate");
  public static UniqueString OP_sf   = UniqueString.uniqueStringOf("$SF");
  public static UniqueString OP_soa  = UniqueString.uniqueStringOf("$SetOfAll");
  public static UniqueString OP_sor  = UniqueString.uniqueStringOf("$SetOfRcds");
  public static UniqueString OP_sof  = UniqueString.uniqueStringOf("$SetOfFcns");
  public static UniqueString OP_sso  = UniqueString.uniqueStringOf("$SubsetOf");
  public static UniqueString OP_tup  = UniqueString.uniqueStringOf("$Tuple");
  public static UniqueString OP_te   = UniqueString.uniqueStringOf("$TemporalExists");
  public static UniqueString OP_tf   = UniqueString.uniqueStringOf("$TemporalForall");
  public static UniqueString OP_uc   = UniqueString.uniqueStringOf("$UnboundedChoose");
  public static UniqueString OP_ue   = UniqueString.uniqueStringOf("$UnboundedExists");
  public static UniqueString OP_uf   = UniqueString.uniqueStringOf("$UnboundedForall");
  public static UniqueString OP_wf   = UniqueString.uniqueStringOf("$WF");

  /*************************************************************************
  * The following added by LL 2-3 Aug 2007.                                *
  *************************************************************************/
  public static UniqueString OP_nop  = UniqueString.uniqueStringOf("$Nop");
  public static UniqueString OP_qed     = UniqueString.uniqueStringOf("$Qed");
  public static UniqueString OP_pfcase  = UniqueString.uniqueStringOf("$Pfcase");
  public static UniqueString OP_have    = UniqueString.uniqueStringOf("$Have");
  public static UniqueString OP_take    = UniqueString.uniqueStringOf("$Take");
  public static UniqueString OP_pick    = UniqueString.uniqueStringOf("$Pick");
  public static UniqueString OP_witness = 
    UniqueString.uniqueStringOf("$Witness");

  /*************************************************************************
  * OP_suffices added by LL 16 Feb 2009.                                   *
  *************************************************************************/
  public static UniqueString OP_suffices  = UniqueString.uniqueStringOf("$Suffices");
  
  /*************************************************************************
  * OP_prime added by LL 2 Dec 2012.                                       *
  *************************************************************************/
  public static UniqueString OP_prime  = UniqueString.uniqueStringOf("'");

}
