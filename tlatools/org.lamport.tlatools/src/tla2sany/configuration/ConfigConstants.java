/***************************************************************************
* This file seems to contain constants that are used to initialize the     *
* semantic analysis.  This includes information about built-in operators.  *
* A parser defined by config.jj apparently parses the string               *
* defaultConfig to extract this information.                               *
***************************************************************************/
// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

// Last modified on Mon 16 February 2009 at 10:03:01 PST by lamport

package tla2sany.configuration;

import tla2sany.parser.Operator;
import tla2sany.parser.Operators;

public interface ConfigConstants {
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
  int OPID = 21;
  int NUMBER = 22;
  int RESTRICTED = 23;

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
    * This is used in config/Configuration.java to create OpDefNode        *
    * objects for each built-in operator, which are put in the             *
    * Context.initialContext table.                                        *
    ***********************************************************************/
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
  
  /**
   * Canonical operators & symbols with their defining characteristics:
   * symbol text, low precedence, high precedence, associativity, fix type.
   */
  Operator[] CanonicalOperators = {
    new Operator("[",             160, 160, Operators.assocLeft, Operators.postfix),
    new Operator(".",             170, 170, Operators.assocLeft, Operators.infix),
    new Operator("'",             150, 150, Operators.assocNone, Operators.postfix),
    new Operator("^",             140, 140, Operators.assocNone, Operators.infix),
    new Operator("/",             130, 130, Operators.assocNone, Operators.infix),
    new Operator("*",             130, 130, Operators.assocLeft, Operators.infix),
    new Operator("-",             110, 110, Operators.assocLeft, Operators.infix),
    new Operator("-.",            120, 120, Operators.assocNone, Operators.prefix),
    new Operator("+",             100, 100, Operators.assocLeft, Operators.infix),
    new Operator("=",             50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\lnot",        40,  40,  Operators.assocLeft, Operators.prefix),
    new Operator("\\land",        30,  30,  Operators.assocLeft, Operators.infix),
    new Operator("\\lor",         30,  30,  Operators.assocLeft, Operators.infix),
    new Operator("~>",            20,  20,  Operators.assocNone, Operators.infix),
    new Operator("=>",            10,  10,  Operators.assocNone, Operators.infix),
    new Operator("[]",            40,  150, Operators.assocNone, Operators.prefix),
    new Operator("<>",            40,  150, Operators.assocNone, Operators.prefix),
    new Operator("ENABLED",       40,  150, Operators.assocNone, Operators.prefix),
    new Operator("UNCHANGED",     40,  150, Operators.assocNone, Operators.prefix),
    new Operator("SUBSET",        100, 130, Operators.assocNone, Operators.prefix),
    new Operator("UNION",         100, 130, Operators.assocNone, Operators.prefix),
    new Operator("DOMAIN",        100, 130, Operators.assocNone, Operators.prefix),
    new Operator("^+",            150, 150, Operators.assocNone, Operators.postfix),
    new Operator("^*",            150, 150, Operators.assocNone, Operators.postfix),
    new Operator("^#",            150, 150, Operators.assocNone, Operators.postfix),
    new Operator("\\cdot",        50,  140, Operators.assocLeft, Operators.infix),
    new Operator("\\equiv",       20,  20,  Operators.assocNone, Operators.infix),
    new Operator("-+->",          20,  20,  Operators.assocNone, Operators.infix),
    new Operator("/=",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\subseteq",    50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\in",          50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\notin",       50,  50,  Operators.assocNone, Operators.infix),
    new Operator("<",             50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\leq",         50,  50,  Operators.assocNone, Operators.infix),
    new Operator(">",             50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\geq",         50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\times",       100, 130, Operators.assocLeft, Operators.nfix),
    new Operator("\\",            80,  80,  Operators.assocNone, Operators.infix),
    new Operator("\\intersect",   80,  80,  Operators.assocLeft, Operators.infix),
    new Operator("\\union",       80,  80,  Operators.assocLeft, Operators.infix),
    new Operator("...",           90,  90,  Operators.assocNone, Operators.infix),
    new Operator("..",            90,  90,  Operators.assocNone, Operators.infix),
    new Operator("|",             100, 110, Operators.assocLeft, Operators.infix),
    new Operator("||",            100, 110, Operators.assocLeft, Operators.infix),
    new Operator("&&",            130, 130, Operators.assocLeft, Operators.infix),
    new Operator("&",             130, 130, Operators.assocLeft, Operators.infix),
    new Operator("$$",            90,  130, Operators.assocLeft, Operators.infix),
    new Operator("$",             90,  130, Operators.assocLeft, Operators.infix),
    new Operator("??",            90,  130, Operators.assocLeft, Operators.infix),
    new Operator("%%",            100, 110, Operators.assocLeft, Operators.infix),
    new Operator("%",             100, 110, Operators.assocNone, Operators.infix),
    new Operator("##",            90,  130, Operators.assocLeft, Operators.infix),
    new Operator("++",            100, 100, Operators.assocLeft, Operators.infix),
    new Operator("--",            110, 110, Operators.assocLeft, Operators.infix),
    new Operator("**",            130, 130, Operators.assocLeft, Operators.infix),
    new Operator("//",            130, 130, Operators.assocNone, Operators.infix),
    new Operator("^^",            140, 140, Operators.assocNone, Operators.infix),
    new Operator("@@",            60,  60,  Operators.assocLeft, Operators.infix),
    new Operator("!!",            90,  130, Operators.assocNone, Operators.infix),
    new Operator("|-",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("|=",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("-|",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("=|",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("<:",            70,  70,  Operators.assocNone, Operators.infix),
    new Operator(":>",            70,  70,  Operators.assocNone, Operators.infix),
    new Operator(":=",            50,  50,  Operators.assocNone, Operators.infix),
    new Operator("::=",           50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\oplus",       100, 100, Operators.assocLeft, Operators.infix),
    new Operator("\\ominus",      110, 110, Operators.assocLeft, Operators.infix),
    new Operator("\\odot",        130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\oslash",      130, 130, Operators.assocNone, Operators.infix),
    new Operator("\\otimes",      130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\uplus",       90,  130, Operators.assocLeft, Operators.infix),
    new Operator("\\sqcap",       90,  130, Operators.assocLeft, Operators.infix),
    new Operator("\\sqcup",       90,  130, Operators.assocLeft, Operators.infix),
    new Operator("\\div",         130, 130, Operators.assocNone, Operators.infix),
    new Operator("\\wr",          90,  140, Operators.assocNone, Operators.infix),
    new Operator("\\star",        130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\o",           130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\bigcirc",     130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\bullet",      130, 130, Operators.assocLeft, Operators.infix),
    new Operator("\\prec",        50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\succ",        50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\preceq",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\succeq",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sim",         50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\simeq",       50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\ll",          50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\gg",          50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\asymp",       50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\subset",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\supset",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\supseteq",    50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\approx",      50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\cong",        50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sqsubset",    50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sqsubseteq",  50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sqsupset",    50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\sqsupseteq",  50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\doteq",       50,  50,  Operators.assocNone, Operators.infix),
    new Operator("\\propto",      50,  50,  Operators.assocNone, Operators.infix),
  };
  
  /*
   * Different ways of writing the same operator. The zeroeth item is the
   * canonical way.
   */
  String[][] OperatorSynonyms = new String[][] {
    new String[] {"\\lnot", "~", "\\neg"},
    new String[] {"\\land", "/\\"},
    new String[] {"\\lor", "\\/"},
    new String[] {"\\equiv", "<=>"},
    new String[] {"/=", "#"},
    new String[] {"\\leq", "<=", "=<"},
    new String[] {"\\geq", ">="},
    // The \mod synonym doesn't seem to be recognized in other parts of the
    // code but keeping it here because it was in the original config.
    new String[] {"%", "\\mod"},
    new String[] {"\\times", "\\X"},
    new String[] {"\\intersect", "\\cap"},
    new String[] {"\\union", "\\cup"},
    new String[] {"\\o", "\\circ"},
    new String[] {"\\oplus", "(+)"},
    new String[] {"\\ominus", "(-)"},
    new String[] {"\\odot", "(.)"},
    new String[] {"\\oslash", "(/)"},
    new String[] {"\\otimes", "(\\X)"},
  };
}
