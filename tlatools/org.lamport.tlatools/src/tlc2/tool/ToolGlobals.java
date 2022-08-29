// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Thu  2 Aug 2007 at 10:19:44 PST by lamport 
//      modified on Fri Sep 22 21:43:08 PDT 2000 by yuanyu 

package tlc2.tool;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpDefNode;
import util.UniqueString;

public interface ToolGlobals extends ASTConstants {
    /**
     * This interface provides useful globals for the implementation
     * of the tools.
     */
    // SZ 11.04.2009: changed the method to the equivalent
    OpDefNode EXCEPT_AT = new OpDefNode(UniqueString.uniqueStringOf("@"));

    /* Prefix operators */
    UniqueString OP_lnot = UniqueString.uniqueStringOf("\\lnot");
    UniqueString OP_subset = UniqueString.uniqueStringOf("SUBSET");
    UniqueString OP_union = UniqueString.uniqueStringOf("UNION");
    UniqueString OP_domain = UniqueString.uniqueStringOf("DOMAIN");
    UniqueString OP_box = UniqueString.uniqueStringOf("[]");
    UniqueString OP_diamond = UniqueString.uniqueStringOf("<>");
    UniqueString OP_enabled = UniqueString.uniqueStringOf("ENABLED");
    UniqueString OP_unchanged = UniqueString.uniqueStringOf("UNCHANGED");

    /* Infix operators */
    UniqueString OP_eq = UniqueString.uniqueStringOf("=");
    UniqueString OP_land = UniqueString.uniqueStringOf("\\land");
    UniqueString OP_lor = UniqueString.uniqueStringOf("\\lor");
    UniqueString OP_implies = UniqueString.uniqueStringOf("=>");
    UniqueString OP_cdot = UniqueString.uniqueStringOf("\\cdot");
    UniqueString OP_equiv = UniqueString.uniqueStringOf("\\equiv");
    UniqueString OP_leadto = UniqueString.uniqueStringOf("~>");
    UniqueString OP_arrow = UniqueString.uniqueStringOf("-+->");
    UniqueString OP_noteq = UniqueString.uniqueStringOf("/=");
    UniqueString OP_subseteq = UniqueString.uniqueStringOf("\\subseteq");
    UniqueString OP_in = UniqueString.uniqueStringOf("\\in");
    UniqueString OP_notin = UniqueString.uniqueStringOf("\\notin");
    UniqueString OP_setdiff = UniqueString.uniqueStringOf("\\");
    UniqueString OP_cap = UniqueString.uniqueStringOf("\\intersect");
    UniqueString OP_cup = UniqueString.uniqueStringOf("\\union");

    /* Below are not built-in operators,  but are useful definitions. */
    UniqueString OP_dotdot = UniqueString.uniqueStringOf("..");
    UniqueString OP_plus = UniqueString.uniqueStringOf("+");
    UniqueString OP_minus = UniqueString.uniqueStringOf("-");
    UniqueString OP_times = UniqueString.uniqueStringOf("*");
    UniqueString OP_lt = UniqueString.uniqueStringOf("<");
    UniqueString OP_leq = UniqueString.uniqueStringOf("\\leq");
    UniqueString OP_gt = UniqueString.uniqueStringOf(">");
    UniqueString OP_geq = UniqueString.uniqueStringOf("\\geq");

    /* Postfix operators */
    UniqueString OP_prime = UniqueString.uniqueStringOf("'");

    /* Opcodes of level 0 */
    int OPCODE_bc = 1;
    int OPCODE_be = 2;
    int OPCODE_bf = 3;
    int OPCODE_case = 4;
    int OPCODE_cp = 5;
    int OPCODE_cl = 6;
    int OPCODE_dl = 7;
    int OPCODE_exc = 8;
    int OPCODE_fa = 9;
    int OPCODE_fc = 10;
    int OPCODE_ite = 11;
    int OPCODE_nrfs = 12;
    int OPCODE_pair = 13;
    int OPCODE_rc = 14;
    int OPCODE_rs = 15;
    int OPCODE_rfs = 16;
    int OPCODE_seq = 17;
    int OPCODE_se = 18;
    int OPCODE_soa = 19;
    int OPCODE_sor = 20;
    int OPCODE_sof = 21;
    int OPCODE_sso = 22;
    int OPCODE_tup = 23;
    int OPCODE_uc = 24;
    int OPCODE_ue = 25;
    int OPCODE_uf = 26;

    /* Prefix opcode of level 0 */
    int OPCODE_lnot = OPCODE_uf + 1;
    int OPCODE_neg = OPCODE_uf + 2;
    int OPCODE_subset = OPCODE_uf + 3;
    int OPCODE_union = OPCODE_uf + 4;
    int OPCODE_domain = OPCODE_uf + 5;
    int OPCODE_enabled = OPCODE_uf + 8;

    /* Infix opcode of level 0 */
    int OPCODE_eq = OPCODE_enabled + 1;
    int OPCODE_land = OPCODE_enabled + 2;
    int OPCODE_lor = OPCODE_enabled + 3;
    int OPCODE_implies = OPCODE_enabled + 4;
    int OPCODE_equiv = OPCODE_enabled + 5;
    int OPCODE_noteq = OPCODE_enabled + 6;
    int OPCODE_subseteq = OPCODE_enabled + 7;
    int OPCODE_in = OPCODE_enabled + 8;
    int OPCODE_notin = OPCODE_enabled + 9;
    int OPCODE_setdiff = OPCODE_enabled + 10;
    int OPCODE_cap = OPCODE_enabled + 11;
    int OPCODE_nop = OPCODE_enabled + 12;
    /***********************************************************************
     * Added by LL on 2 Aug 2007.                                           *
     ***********************************************************************/

    int OPCODE_cup = OPCODE_enabled + 13;

    /* Opcodes of level 2 */
    int OPCODE_prime = OPCODE_cup + 1;
    int OPCODE_unchanged = OPCODE_cup + 2;
    int OPCODE_aa = OPCODE_cup + 3;
    int OPCODE_sa = OPCODE_cup + 4;
    int OPCODE_cdot = OPCODE_cup + 5;

    /* Opcodes of level 3 */
    int OPCODE_sf = OPCODE_cdot + 1;
    int OPCODE_wf = OPCODE_cdot + 2;
    int OPCODE_te = OPCODE_cdot + 3;
    int OPCODE_tf = OPCODE_cdot + 4;
    int OPCODE_leadto = OPCODE_cdot + 5;
    int OPCODE_arrow = OPCODE_cdot + 6;
    int OPCODE_box = OPCODE_cdot + 7;
    int OPCODE_diamond = OPCODE_cdot + 8;

}
