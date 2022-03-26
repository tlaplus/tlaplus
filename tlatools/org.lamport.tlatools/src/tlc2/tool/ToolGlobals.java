// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Thu  2 Aug 2007 at 10:19:44 PST by lamport 
//      modified on Fri Sep 22 21:43:08 PDT 2000 by yuanyu 

package tlc2.tool;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpDefNode;

public interface ToolGlobals extends ASTConstants {
  /**
   * This interface provides useful globals for the implementation
   * of the tools.
   */
  // SZ 11.04.2009: changed the method to the equivalent 
  public static final OpDefNode EXCEPT_AT = new OpDefNode("@");
  
  // TODO : Most of this is unused?
  
  /* Prefix operators */
  public static final String OP_lnot = ("\\lnot");
  public static final String OP_subset = ("SUBSET");
  public static final String OP_union = ("UNION");
  public static final String OP_domain = ("DOMAIN");
  public static final String OP_box = ("[]");
  public static final String OP_diamond = ("<>");
  public static final String OP_enabled = ("ENABLED");
  public static final String OP_unchanged = ("UNCHANGED");

  /* Infix operators */
  public static final String OP_eq = ("=");
  public static final String OP_land = ("\\land");
  public static final String OP_lor = ("\\lor");
  public static final String OP_implies = ("=>");
  public static final String OP_cdot = ("\\cdot");
  public static final String OP_equiv = ("\\equiv");
  public static final String OP_leadto = ("~>");
  public static final String OP_arrow = ("-+->");
  public static final String OP_noteq = ("/=");
  public static final String OP_subseteq = ("\\subseteq");
  public static final String OP_in = ("\\in");
  public static final String OP_notin = ("\\notin");
  public static final String OP_setdiff = ("\\");
  public static final String OP_cap = ("\\intersect");
  public static final String OP_cup = ("\\union");

  /* Below are not built-in operators,  but are useful definitions. */
  public static final String OP_dotdot = ("..");  
  public static final String OP_plus = ("+");
  public static final String OP_minus = ("-");
  public static final String OP_times = ("*");
  public static final String OP_lt = ("<");
  public static final String OP_leq = ("\\leq");
  public static final String OP_gt = (">");    
  public static final String OP_geq = ("\\geq");

  /* Postfix operators */
  public static final String OP_prime = ("'");

  /* Opcodes of level 0 */
  public static final int OPCODE_bc   = 1;
  public static final int OPCODE_be   = 2;
  public static final int OPCODE_bf   = 3;
  public static final int OPCODE_case = 4;
  public static final int OPCODE_cp   = 5;
  public static final int OPCODE_cl   = 6;
  public static final int OPCODE_dl   = 7;
  public static final int OPCODE_exc  = 8;
  public static final int OPCODE_fa   = 9;
  public static final int OPCODE_fc   = 10;
  public static final int OPCODE_ite  = 11;
  public static final int OPCODE_nrfs = 12;
  public static final int OPCODE_pair = 13;
  public static final int OPCODE_rc   = 14;
  public static final int OPCODE_rs   = 15;
  public static final int OPCODE_rfs  = 16;
  public static final int OPCODE_seq  = 17;
  public static final int OPCODE_se   = 18;
  public static final int OPCODE_soa  = 19;
  public static final int OPCODE_sor  = 20;
  public static final int OPCODE_sof  = 21;
  public static final int OPCODE_sso  = 22;
  public static final int OPCODE_tup  = 23;
  public static final int OPCODE_uc   = 24;
  public static final int OPCODE_ue   = 25;
  public static final int OPCODE_uf   = 26;

  /* Prefix opcode of level 0 */
  public static final int OPCODE_lnot    = OPCODE_uf + 1;
  public static final int OPCODE_neg     = OPCODE_uf + 2;
  public static final int OPCODE_subset  = OPCODE_uf + 3;
  public static final int OPCODE_union   = OPCODE_uf + 4;
  public static final int OPCODE_domain  = OPCODE_uf + 5;
  public static final int OPCODE_enabled = OPCODE_uf + 8;

  /* Infix opcode of level 0 */
  public static final int OPCODE_eq       = OPCODE_enabled + 1;
  public static final int OPCODE_land     = OPCODE_enabled + 2;
  public static final int OPCODE_lor      = OPCODE_enabled + 3;
  public static final int OPCODE_implies  = OPCODE_enabled + 4;
  public static final int OPCODE_equiv    = OPCODE_enabled + 5;
  public static final int OPCODE_noteq    = OPCODE_enabled + 6;
  public static final int OPCODE_subseteq = OPCODE_enabled + 7;
  public static final int OPCODE_in       = OPCODE_enabled + 8;
  public static final int OPCODE_notin    = OPCODE_enabled + 9;
  public static final int OPCODE_setdiff  = OPCODE_enabled + 10;
  public static final int OPCODE_cap      = OPCODE_enabled + 11;
  public static final int OPCODE_nop      = OPCODE_enabled + 12;
    /***********************************************************************
    * Added by LL on 2 Aug 2007.                                           *
    ***********************************************************************/
    
  public static final int OPCODE_cup      = OPCODE_enabled + 13;
  
  /* Opcodes of level 2 */
  public static final int OPCODE_prime     = OPCODE_cup + 1;
  public static final int OPCODE_unchanged = OPCODE_cup + 2;
  public static final int OPCODE_aa        = OPCODE_cup + 3;
  public static final int OPCODE_sa        = OPCODE_cup + 4;
  public static final int OPCODE_cdot      = OPCODE_cup + 5;  
  
  /* Opcodes of level 3 */
  public static final int OPCODE_sf      = OPCODE_cdot + 1;
  public static final int OPCODE_wf      = OPCODE_cdot + 2;
  public static final int OPCODE_te      = OPCODE_cdot + 3;
  public static final int OPCODE_tf      = OPCODE_cdot + 4;
  public static final int OPCODE_leadto  = OPCODE_cdot + 5;
  public static final int OPCODE_arrow   = OPCODE_cdot + 6;
  public static final int OPCODE_box     = OPCODE_cdot + 7;
  public static final int OPCODE_diamond = OPCODE_cdot + 8;

}
