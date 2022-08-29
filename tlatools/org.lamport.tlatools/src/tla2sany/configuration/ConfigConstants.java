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

    // None, verified.
    //\n" +
    //\n" +
    //\n" +
    //\n" +
    //\n" +
    //\n" +
    //\n" +
    //"operator ? 90 130 Left infix\n" +  // Removed requested by Leslie (16 Feb. 01)
    // \n" +
    // \n" +
    // subseteq is builtin
    //\n" +
    //\n" +
    //\n" +
    //\n" +
    //\n" +
    //
    // arity corrected from 1 to -1 DRJ 20 Nov '00
    // Added by DRJ 1 Oct '00
    /***********************************************************************
     * $Suffices added by LL 16 Feb 2009.                                   *
     ***********************************************************************/
    String defaultConfig =
            /***********************************************************************
             * This is used in config/Configuration.java to create Operator         *
             * objects for each operator, which are put in the hashtable            *
             * Operators.BuiltinTable.                                              *
             ***********************************************************************/
            """
                    operator [ 160 160 Left postfix\s
                    operator . 170 170 Left infix\s
                    operator ' 150 150 None postfix
                    operator ^ 140 140 None infix
                    operator / 130 130 None infix
                    operator * 130 130 Left infix
                    operator - 110 110 Left infix
                    operator -. 120 120 None prefix
                    operator + 100 100 Left infix
                    operator = 50 50 None infix
                    operator \\lnot 40 40 Left prefix\s
                    synonym  ~ \\lnot
                    synonym \\neg \\lnot
                    operator \\land 30 30 Left infix
                    synonym  /\\ \\land
                    operator \\lor 30 30 Left infix
                    synonym  \\/ \\lor
                    operator ~> 20 20 None infix
                    operator => 10 10  None infix
                    operator [] 40 150 None prefix\s
                    operator <> 40 150 None prefix\s
                    operator ENABLED 40 150 None prefix\s
                    operator UNCHANGED 40 150 None prefix\s
                    operator SUBSET 100 130 None prefix\s
                    operator UNION 100 130 None prefix\s
                    operator DOMAIN 100 130 None prefix\s
                    operator ^+ 150 150 None postfix
                    operator ^* 150 150 None postfix
                    operator ^# 150 150 None postfix
                    operator \\cdot 50 140  Left infix
                    operator \\equiv 20 20  None infix
                    synonym <=> \\equiv
                    operator -+-> 20 20 None infix
                    operator /= 50 50 None infix
                    synonym # /=
                    operator \\subseteq 50 50 None infix
                    operator \\in 50 50 None infix
                    operator \\notin 50 50 None infix
                    operator < 50 50 None infix
                    operator \\leq 50 50 None infix
                    synonym <= \\leq
                    synonym =< \\leq
                    operator > 50 50 None infix
                    operator \\geq 50 50 None infix
                    synonym >= \\geq
                    operator \\times 100 130 Left nfix
                    synonym  \\X \\times
                    operator \\ 80 80 None infix
                    operator \\intersect 80 80 Left infix
                    synonym \\cap \\intersect\s
                    operator \\union 80 80 Left infix
                    synonym \\cup \\union
                    operator ... 90 90 None infix
                    operator .. 90 90 None infix
                    operator | 100 110 Left infix
                    operator || 100 110 Left infix
                    operator && 130 130 Left infix
                    operator & 130 130 Left infix
                    operator $$ 90 130 Left infix
                    operator $ 90 130 Left infix
                    operator ?? 90 130 Left infix
                    operator %% 100 110 Left infix
                    operator % 100 110 None infix
                    synonym \\mod %
                    operator ## 90 130 Left infix
                    operator ++ 100 100 Left infix
                    operator -- 110 110 Left infix
                    operator ** 130 130 Left infix
                    operator // 130 130 None infix
                    operator ^^ 140 140 None infix
                    operator @@ 60 60 Left infix
                    operator !! 90 130 None infix
                    operator |- 50 50 None infix
                    operator |= 50 50 None infix
                    operator -| 50 50 None infix
                    operator =| 50 50 None infix
                    operator <: 70 70 None infix
                    operator :> 70 70 None infix
                    operator := 50 50 None infix
                    operator ::= 50 50 None infix
                    operator \\oplus 100 100 Left infix
                    synonym (+) \\oplus
                    operator \\ominus 110 110 Left infix
                    synonym (-) \\ominus
                    operator \\odot 130 130 Left infix
                    synonym (.) \\odot
                    operator \\oslash 130 130 None infix
                    synonym (/) \\oslash
                    operator \\otimes 130 130 Left infix
                    synonym (\\X) \\otimes
                    operator \\uplus 90 130 Left infix
                    operator \\sqcap 90 130 Left infix
                    operator \\sqcup 90 130 Left infix
                    operator \\div 130 130 None infix
                    operator \\wr 90 140 None infix
                    operator \\star 130 130 Left infix
                    operator \\o 130 130 Left infix
                    synonym  \\circ \\o\s
                    operator \\bigcirc 130 130 Left infix
                    operator \\bullet 130 130 Left infix
                    operator \\prec 50 50 None infix
                    operator \\succ 50 50 None infix
                    operator \\preceq 50 50 None infix
                    operator \\succeq 50 50 None infix
                    operator \\sim 50 50 None infix
                    operator \\simeq 50 50 None infix
                    operator \\ll 50 50 None infix
                    operator \\gg 50 50 None infix
                    operator \\asymp 50 50 None infix
                    operator \\subset 50 50 None infix
                    operator \\supset 50 50 None infix
                    operator \\supseteq 50 50 None infix
                    operator \\approx 50 50 None infix
                    operator \\cong 50 50 None infix
                    operator \\sqsubset 50 50 None infix
                    operator \\sqsubseteq 50 50 None infix
                    operator \\sqsupset 50 50 None infix
                    operator \\sqsupseteq 50 50 None infix
                    operator \\doteq 50 50 None infix
                    operator \\propto 50 50 None infix
                    builtin STRING    $$_string     constant
                    builtin FALSE     $$_false      constant
                    builtin TRUE      $$_true       constant
                    builtin BOOLEAN   $$_boolean    constant
                    builtin =         $$_equal        infix
                    builtin /=        $$_notEqual     infix
                    builtin .         $$_dot          infix
                    builtin '         $$_prime        postfix
                    builtin \\lnot     $$_not          prefix
                    builtin \\neg      $$_neg          prefix
                    builtin \\land     $$_and          infix
                    builtin \\lor      $$_or           infix
                    builtin \\equiv    $$_equivalent   infix
                    builtin =>        $$_implies      infix
                    builtin SUBSET     $$_subset      prefix
                    builtin UNION      $$_union       prefix
                    builtin DOMAIN     $$_domain      prefix
                    builtin \\subseteq  $$_subseteq    infix\s
                    builtin \\in        $$_in          infix\s
                    builtin \\notin     $$_notin       infix\s
                    builtin \\          $$_setdiff     infix\s
                    builtin \\intersect $$_setinter    infix\s
                    builtin \\union     $$_setunion    infix\s
                    builtin \\times     $$_times       infix\s
                    builtin ~>         $$_leadsTo     infix\s
                    builtin []         $$_box         prefix
                    builtin <>         $$_diamond     prefix
                    builtin ENABLED    $$_enabled     prefix
                    builtin UNCHANGED  $$_unchanged   prefix
                    builtin \\cdot     $$_cdot        infix\s
                    builtin -+->       $$_arrow       infix\s
                    builtin $AngleAct                $$_null   2
                    builtin $BoundedChoose           $$_null  -1
                    builtin $BoundedExists           $$_null  -1
                    builtin $BoundedForall           $$_null  -1
                    builtin $CartesianProd           $$_null  -1
                    builtin $Case                    $$_null  -1
                    builtin $ConjList                $$_null  -1
                    builtin $DisjList                $$_null  -1
                    builtin $Except                  $$_null  -1
                    builtin $FcnApply                $$_null   2
                    builtin $FcnConstructor          $$_null  -1
                    builtin $IfThenElse              $$_null   3
                    builtin $NonRecursiveFcnSpec     $$_null   1
                    builtin $Pair                    $$_null   2
                    builtin $RcdConstructor          $$_null  -1
                    builtin $RcdSelect               $$_null   2
                    builtin $RecursiveFcnSpec        $$_null   1
                    builtin $Seq                     $$_null  -1
                    builtin $SetEnumerate            $$_null  -1
                    builtin $SetOfAll                $$_null  -1
                    builtin $SetOfFcns               $$_null  -1
                    builtin $SetOfRcds               $$_null  -1
                    builtin $SF                      $$_null   2
                    builtin $SquareAct               $$_null   2
                    builtin $SubsetOf                $$_null   1
                    builtin $TemporalExists          $$_null   1
                    builtin $TemporalForall          $$_null   1
                    builtin $TemporalWhile           $$_null   2
                    builtin $Tuple                   $$_null  -1
                    builtin $UnboundedChoose         $$_null   1
                    builtin $UnboundedExists         $$_null   1
                    builtin $UnboundedForall         $$_null   1
                    builtin $WF                      $$_null   2
                    builtin $Nop                     $$_null   1
                    builtin $Qed                     $$_null   0
                    builtin $Pfcase                  $$_null   1
                    builtin $Have                    $$_null   1
                    builtin $Take                    $$_null   1
                    builtin $Pick                    $$_null   1
                    builtin $Witness                 $$_null   -1
                    builtin $Suffices                $$_null   1
                    """;
}

