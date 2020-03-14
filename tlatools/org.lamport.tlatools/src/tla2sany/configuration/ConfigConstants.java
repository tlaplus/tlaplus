/***************************************************************************
* This file seems to contain constants that are used to initialize the     *
* semantic analysis.  This includes information about built-in operators.  *
* A parser defined by config.jj apparently parses the string               *
* defaultConfig to extract this information.                               *
***************************************************************************/
// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

// Last modified on Mon 16 February 2009 at 10:03:01 PST by lamport

package tla2sany.configuration;

interface ConfigConstants {
  int nada = 0;
  int infixOP = 1;
  int prefixOP = 2;
  int postfixOP = 3;
  int preINfixOP = 4;

  int leftAssoc = 10;
  int rightAssoc = 11;
  int noAssoc = 12;

  int EOF = 0;
  int SINGLE_LINE = 4;
  int CONSTANT = 7;
  int OPERATOR = 8;
  int INFIX = 9;
  int POSTFIX = 10;
  int PREFIX = 11;
  int NFIX = 12;
  int NOTOP = 13;
  int SYNONYM = 14;
  int LEFTASSOC = 15;
  int RIGHTASSOC = 16;
  int NOASSOC = 17;
  int BUILTIN = 18;
  int OPCHAR = 19;
  int LETTER = 20;
  int OPID = 21;
  int NUMBER = 22;
  int RESTRICTED = 23;

  int DEFAULT = 0;
  int IN_COMMENT = 1;

  String[] tokenImage = {
    "<EOF>",
    "\" \"",
    "\"\\t\"",
    "\"\\n\"",
    "\"(*\"",
    "\"*)\"",
    "<token of kind 6>",
    "<CONSTANT>",
    "<OPERATOR>",
    "<INFIX>",
    "<POSTFIX>",
    "<PREFIX>",
    "<NFIX>",
    "<NOTOP>",
    "<SYNONYM>",
    "<LEFTASSOC>",
    "<RIGHTASSOC>",
    "<NOASSOC>",
    "<BUILTIN>",
    "<OPCHAR>",
    "<LETTER>",
    "<OPID>",
    "<NUMBER>",
    "<RESTRICTED>",
  };

  String defaultConfig =
    /***********************************************************************
    * This is used in config/Configuration.java to create Operator         *
    * objects for each operator, which are put in the hashtable            *
    * Operators.BuiltinTable.                                              *
    ***********************************************************************/
    "operator [ 160 160 Left postfix \n" +
    "operator . 170 170 Left infix \n" +
    "operator ' 150 150 None postfix\n" +
    "operator ^ 140 140 None infix\n" +  // None, verified.
    "operator / 130 130 None infix\n" +
    "operator * 130 130 Left infix\n" +
    "operator - 110 110 Left infix\n" +
    "operator -. 120 120 None prefix\n" +
    "operator + 100 100 Left infix\n" +
    "operator = 50 50 None infix\n" +
    "operator \\lnot 40 40 Left prefix \n" +
    "synonym  ~ \\lnot\n" +
    "synonym \\neg \\lnot\n" +
    "operator \\land 30 30 Left infix\n" +
    "synonym  /\\ \\land\n" +
    "operator \\lor 30 30 Left infix\n" +
    "synonym  \\/ \\lor\n" +
    "operator ~> 20 20 None infix\n" +
    "operator => 10 10  None infix\n" +
    //\n" +
    "operator [] 40 150 None prefix \n" +
    "operator <> 40 150 None prefix \n" +
    "operator ENABLED 40 150 None prefix \n" +
    "operator UNCHANGED 40 150 None prefix \n" +
    "operator SUBSET 100 130 None prefix \n" +
    "operator UNION 100 130 None prefix \n" +
    "operator DOMAIN 100 130 None prefix \n" +
    //\n" +
    "operator ^+ 150 150 None postfix\n" +
    "operator ^* 150 150 None postfix\n" +
    "operator ^# 150 150 None postfix\n" +
    //\n" +
    "operator \\cdot 50 140  Left infix\n" +
    //\n" +
    "operator \\equiv 20 20  None infix\n" +
    "synonym <=> \\equiv\n" +
    //\n" +
    "operator -+-> 20 20 None infix\n" +
    "operator /= 50 50 None infix\n" +
    "synonym # /=\n" +
    "operator \\subseteq 50 50 None infix\n" +
    "operator \\in 50 50 None infix\n" +
    "operator \\notin 50 50 None infix\n" +
    "operator < 50 50 None infix\n" +
    "operator \\leq 50 50 None infix\n" +
    "synonym <= \\leq\n" +
    "synonym =< \\leq\n" +
    "operator > 50 50 None infix\n" +
    "operator \\geq 50 50 None infix\n" +
    "synonym >= \\geq\n" +
    //\n" +
    "operator \\times 100 130 Left nfix\n" +
    "synonym  \\X \\times\n" +
    "operator \\ 80 80 None infix\n" +
    "operator \\intersect 80 80 Left infix\n" +
    "synonym \\cap \\intersect \n" +
    "operator \\union 80 80 Left infix\n" +
    "synonym \\cup \\union\n" +
    //\n" +
    "operator ... 90 90 None infix\n" +
    "operator .. 90 90 None infix\n" +
    "operator | 100 110 Left infix\n" +
    "operator || 100 110 Left infix\n" +
    "operator && 130 130 Left infix\n" +
    "operator & 130 130 Left infix\n" +
    "operator $$ 90 130 Left infix\n" +
    "operator $ 90 130 Left infix\n" +  
    "operator ?? 90 130 Left infix\n" +
    //"operator ? 90 130 Left infix\n" +  // Removed requested by Leslie (16 Feb. 01)
    "operator %% 100 110 Left infix\n" +
    "operator % 100 110 None infix\n" +
    "synonym \\mod %\n" +
    "operator ## 90 130 Left infix\n" +
    "operator ++ 100 100 Left infix\n" +
    "operator -- 110 110 Left infix\n" +
    "operator ** 130 130 Left infix\n" +
    "operator // 130 130 None infix\n" +
    "operator ^^ 140 140 None infix\n" +
    "operator @@ 60 60 Left infix\n" +
    "operator !! 90 130 None infix\n" +
    "operator |- 50 50 None infix\n" +
    "operator |= 50 50 None infix\n" +
    "operator -| 50 50 None infix\n" +
    "operator =| 50 50 None infix\n" +
    "operator <: 70 70 None infix\n" +
    "operator :> 70 70 None infix\n" +
    "operator := 50 50 None infix\n" +
    "operator ::= 50 50 None infix\n" +
// \n" +
    "operator \\oplus 100 100 Left infix\n" +
    "synonym (+) \\oplus\n" +
    "operator \\ominus 110 110 Left infix\n" +
    "synonym (-) \\ominus\n" +
    "operator \\odot 130 130 Left infix\n" +
    "synonym (.) \\odot\n" +
    "operator \\oslash 130 130 None infix\n" +
    "synonym (/) \\oslash\n" +
    "operator \\otimes 130 130 Left infix\n" +
    "synonym (\\X) \\otimes\n" +
// \n" +
    "operator \\uplus 90 130 Left infix\n" +
    "operator \\sqcap 90 130 Left infix\n" +
    "operator \\sqcup 90 130 Left infix\n" +
    "operator \\div 130 130 None infix\n" +
    "operator \\wr 90 140 None infix\n" +
    "operator \\star 130 130 Left infix\n" +
    "operator \\o 130 130 Left infix\n" +
    "synonym  \\circ \\o \n" +
    "operator \\bigcirc 130 130 Left infix\n" +
    "operator \\bullet 130 130 Left infix\n" +
    "operator \\prec 50 50 None infix\n" +
    "operator \\succ 50 50 None infix\n" +
    "operator \\preceq 50 50 None infix\n" +
    "operator \\succeq 50 50 None infix\n" +
    "operator \\sim 50 50 None infix\n" +
    "operator \\simeq 50 50 None infix\n" +
    "operator \\ll 50 50 None infix\n" +
    "operator \\gg 50 50 None infix\n" +
    "operator \\asymp 50 50 None infix\n" +
    "operator \\subset 50 50 None infix\n" + // subseteq is builtin
    "operator \\supset 50 50 None infix\n" +
    "operator \\supseteq 50 50 None infix\n" +
    "operator \\approx 50 50 None infix\n" +
    "operator \\cong 50 50 None infix\n" +
    "operator \\sqsubset 50 50 None infix\n" +
    "operator \\sqsubseteq 50 50 None infix\n" +
    "operator \\sqsupset 50 50 None infix\n" +
    "operator \\sqsupseteq 50 50 None infix\n" +
    "operator \\doteq 50 50 None infix\n" +
    "operator \\propto 50 50 None infix\n" +
    //\n" +
    "builtin STRING    $$_string     constant\n" +
    "builtin FALSE     $$_false      constant\n" +
    "builtin TRUE      $$_true       constant\n" +
    "builtin BOOLEAN   $$_boolean    constant\n" +
    //\n" +
    "builtin =         $$_equal        infix\n" +
    "builtin /=        $$_notEqual     infix\n" +
    //\n" +
    "builtin .         $$_dot          infix\n" +
    "builtin '         $$_prime        postfix\n" +
    "builtin \\lnot     $$_not          prefix\n" +
    "builtin \\neg      $$_neg          prefix\n" +
    "builtin \\land     $$_and          infix\n" +
    "builtin \\lor      $$_or           infix\n" +
    "builtin \\equiv    $$_equivalent   infix\n" +
    "builtin =>        $$_implies      infix\n" +
    //\n" +
    "builtin SUBSET     $$_subset      prefix\n" +
    "builtin UNION      $$_union       prefix\n" +
    "builtin DOMAIN     $$_domain      prefix\n" +
    "builtin \\subseteq  $$_subseteq    infix \n" +
    "builtin \\in        $$_in          infix \n" +
    "builtin \\notin     $$_notin       infix \n" +
    "builtin \\          $$_setdiff     infix \n" +
    "builtin \\intersect $$_setinter    infix \n" +
    "builtin \\union     $$_setunion    infix \n" +
    "builtin \\times     $$_times       infix \n" +
    //\n" +
    "builtin ~>         $$_leadsTo     infix \n" +
    "builtin []         $$_box         prefix\n" +
    "builtin <>         $$_diamond     prefix\n" +
    "builtin ENABLED    $$_enabled     prefix\n" +
    "builtin UNCHANGED  $$_unchanged   prefix\n" +
    "builtin \\cdot     $$_cdot        infix \n" +
    "builtin -+->       $$_arrow       infix \n" +
//
    "builtin $AngleAct                $$_null   2\n" +
    "builtin $BoundedChoose           $$_null  -1\n" +
    "builtin $BoundedExists           $$_null  -1\n" +
    "builtin $BoundedForall           $$_null  -1\n" +
    "builtin $CartesianProd           $$_null  -1\n" +
    "builtin $Case                    $$_null  -1\n" +
    "builtin $ConjList                $$_null  -1\n" +
    "builtin $DisjList                $$_null  -1\n" +
    "builtin $Except                  $$_null  -1\n" + // arity corrected from 1 to -1 DRJ 20 Nov '00
    "builtin $FcnApply                $$_null   2\n" +
    "builtin $FcnConstructor          $$_null  -1\n" +
    "builtin $IfThenElse              $$_null   3\n" +
    "builtin $NonRecursiveFcnSpec     $$_null   1\n" +
    "builtin $Pair                    $$_null   2\n" +
    "builtin $RcdConstructor          $$_null  -1\n" +
    "builtin $RcdSelect               $$_null   2\n" +
    "builtin $RecursiveFcnSpec        $$_null   1\n" +
    "builtin $Seq                     $$_null  -1\n" +
    "builtin $SetEnumerate            $$_null  -1\n" +
    "builtin $SetOfAll                $$_null  -1\n" +
    "builtin $SetOfFcns               $$_null  -1\n" +
    "builtin $SetOfRcds               $$_null  -1\n" + // Added by DRJ 1 Oct '00 
    "builtin $SF                      $$_null   2\n" +
    "builtin $SquareAct               $$_null   2\n" +
    "builtin $SubsetOf                $$_null   1\n" +
    "builtin $TemporalExists          $$_null   1\n" +
    "builtin $TemporalForall          $$_null   1\n" +
    "builtin $TemporalWhile           $$_null   2\n" +
    "builtin $Tuple                   $$_null  -1\n" +
    "builtin $UnboundedChoose         $$_null   1\n" +
    "builtin $UnboundedExists         $$_null   1\n" +
    "builtin $UnboundedForall         $$_null   1\n" +
    "builtin $WF                      $$_null   2\n"   +
    "builtin $Nop                     $$_null   1\n"   +
    "builtin $Qed                     $$_null   0\n"   +
    "builtin $Pfcase                  $$_null   1\n"   +
    "builtin $Have                    $$_null   1\n"   +
    "builtin $Take                    $$_null   1\n"   +
    "builtin $Pick                    $$_null   1\n"   +
    "builtin $Witness                 $$_null   -1\n"  +

    /***********************************************************************
    * $Suffices added by LL 16 Feb 2009.                                   *
    ***********************************************************************/
    "builtin $Suffices                $$_null   1\n"   

  ;
}

