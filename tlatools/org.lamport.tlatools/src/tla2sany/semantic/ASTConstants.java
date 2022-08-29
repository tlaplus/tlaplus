// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// last modified on Mon 16 February 2009 at  9:57:46 PST by lamport 

package tla2sany.semantic;

import util.UniqueString;

public interface ASTConstants {

    /* The following are kinds of SemanticNodes. */
    int ModuleKind = 1;  // Used for ModuleNodes
    int ConstantDeclKind = 2;
    // A kind of OpDeclNode; used for constants
    int VariableDeclKind = 3;
    // A kind of OpDeclNode; used for variables
    int BoundSymbolKind = 4;
    // A kind of OpDeclNode; used for symbols bound by quantifier-like ops
    int UserDefinedOpKind = 5;
    // A kind of OpDefNode; used for OpDefNodes for user-defined ops
    int ModuleInstanceKind = 6;
    // A kind of OpDefNode; used for "M" in M(x) == INSTANCE Foo ...
    int BuiltInKind = 7;
    // A kind of OpDefNode; used only for OpDefNodes of built-in ops
    int OpArgKind = 8;
    int OpApplKind = 9;
    int LetInKind = 10;
    int FormalParamKind = 11;
    int TheoremKind = 12;
    int SubstInKind = 13;
    int AssumeProveKind = 14;
    //  public static final int ProofKind          = 15;
    int NumeralKind = 16;
    int DecimalKind = 17;
    int StringKind = 18;
    int AtNodeKind = 19;
    int AssumeKind = 20;
    int InstanceKind = 21;
    // Used for InstanceNodes, representing an INSTANCE stmt
    // or def (whether named or not). Not to be confused with
    // ModuleInstanceKind above, which represents a name that
    // must not be (re)used for a user-defined operator.
    int NewSymbKind = 22;
    // Added by LL on 15 Mar 2007
    int ThmOrAssumpDefKind = 23;
    // Added by LL on 17 Mar 2007

    /*************************************************************************
     * The following are kinds of OpDeclNode used for a declaration in the    *
     * assumptions list of an AssumeProve.                                    *
     *                                                                        *
     * Added by LL on 22 Mar 2007                                             *
     *************************************************************************/
    int NewConstantKind = 24;
    int NewVariableKind = 25;
    int NewStateKind = 26;
    int NewActionKind = 27;
    int NewTemporalKind = 28;

    int LabelKind = 29;
    int APSubstInKind = 30;
    int UseKind = 31;
    int HideKind = 32;
    int LeafProofKind = 33;
    int NonLeafProofKind = 34;
    int QEDStepKind = 35;
    int DefStepKind = 36;
    int NumberedProofStepKind = 37;


    /*************************************************************************
     * AN array of printable names for the constants defined above.           *
     *************************************************************************/
    String[] kinds = {
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
    UniqueString OP_aa = UniqueString.uniqueStringOf("$AngleAct");
    UniqueString OP_bc = UniqueString.uniqueStringOf("$BoundedChoose");
    UniqueString OP_be = UniqueString.uniqueStringOf("$BoundedExists");
    UniqueString OP_bf = UniqueString.uniqueStringOf("$BoundedForall");
    UniqueString OP_case = UniqueString.uniqueStringOf("$Case");
    UniqueString OP_cp = UniqueString.uniqueStringOf("$CartesianProd");
    UniqueString OP_cl = UniqueString.uniqueStringOf("$ConjList");
    UniqueString OP_dl = UniqueString.uniqueStringOf("$DisjList");
    UniqueString OP_exc = UniqueString.uniqueStringOf("$Except");
    UniqueString OP_fa = UniqueString.uniqueStringOf("$FcnApply");
    UniqueString OP_fc = UniqueString.uniqueStringOf("$FcnConstructor");
    UniqueString OP_ite = UniqueString.uniqueStringOf("$IfThenElse");
    UniqueString OP_nrfs = UniqueString.uniqueStringOf("$NonRecursiveFcnSpec");
    UniqueString OP_pair = UniqueString.uniqueStringOf("$Pair");
    UniqueString OP_rc = UniqueString.uniqueStringOf("$RcdConstructor");
    UniqueString OP_rs = UniqueString.uniqueStringOf("$RcdSelect");
    UniqueString OP_rfs = UniqueString.uniqueStringOf("$RecursiveFcnSpec");
    UniqueString OP_seq = UniqueString.uniqueStringOf("$Seq");
    UniqueString OP_sa = UniqueString.uniqueStringOf("$SquareAct");
    UniqueString OP_se = UniqueString.uniqueStringOf("$SetEnumerate");
    UniqueString OP_sf = UniqueString.uniqueStringOf("$SF");
    UniqueString OP_soa = UniqueString.uniqueStringOf("$SetOfAll");
    UniqueString OP_sor = UniqueString.uniqueStringOf("$SetOfRcds");
    UniqueString OP_sof = UniqueString.uniqueStringOf("$SetOfFcns");
    UniqueString OP_sso = UniqueString.uniqueStringOf("$SubsetOf");
    UniqueString OP_tup = UniqueString.uniqueStringOf("$Tuple");
    UniqueString OP_te = UniqueString.uniqueStringOf("$TemporalExists");
    UniqueString OP_tf = UniqueString.uniqueStringOf("$TemporalForall");
    UniqueString OP_uc = UniqueString.uniqueStringOf("$UnboundedChoose");
    UniqueString OP_ue = UniqueString.uniqueStringOf("$UnboundedExists");
    UniqueString OP_uf = UniqueString.uniqueStringOf("$UnboundedForall");
    UniqueString OP_wf = UniqueString.uniqueStringOf("$WF");

    /*************************************************************************
     * The following added by LL 2-3 Aug 2007.                                *
     *************************************************************************/
    UniqueString OP_nop = UniqueString.uniqueStringOf("$Nop");
    UniqueString OP_qed = UniqueString.uniqueStringOf("$Qed");
    UniqueString OP_pfcase = UniqueString.uniqueStringOf("$Pfcase");
    UniqueString OP_have = UniqueString.uniqueStringOf("$Have");
    UniqueString OP_take = UniqueString.uniqueStringOf("$Take");
    UniqueString OP_pick = UniqueString.uniqueStringOf("$Pick");
    UniqueString OP_witness =
            UniqueString.uniqueStringOf("$Witness");

    /*************************************************************************
     * OP_suffices added by LL 16 Feb 2009.                                   *
     *************************************************************************/
    UniqueString OP_suffices = UniqueString.uniqueStringOf("$Suffices");

    /*************************************************************************
     * OP_prime added by LL 2 Dec 2012.                                       *
     *************************************************************************/
    UniqueString OP_prime = UniqueString.uniqueStringOf("'");

}
