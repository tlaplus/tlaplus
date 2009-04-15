// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Thu  2 Aug 2007 at 10:19:44 PST by lamport 
//      modified on Fri Sep 22 21:43:08 PDT 2000 by yuanyu 

package tlc2.tool;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpDefNode;
import tlc2.value.Value;
import util.UniqueString;

public interface ToolGlobals extends ASTConstants {
  /**
   * This interface provides useful globals for the implementation
   * of the tools.
   */

  public static final Value[] EmptyArgs = new Value[0];
  // SZ 11.04.2009: changed the method to the equivalent 
  public static final OpDefNode EXCEPT_AT = new OpDefNode(UniqueString.uniqueStringOf("@"));
  
  /* Prefix operators */
  public static final UniqueString OP_lnot = UniqueString.uniqueStringOf("\\lnot");
  public static final UniqueString OP_subset = UniqueString.uniqueStringOf("SUBSET");
  public static final UniqueString OP_union = UniqueString.uniqueStringOf("UNION");
  public static final UniqueString OP_domain = UniqueString.uniqueStringOf("DOMAIN");
  public static final UniqueString OP_box = UniqueString.uniqueStringOf("[]");
  public static final UniqueString OP_diamond = UniqueString.uniqueStringOf("<>");
  public static final UniqueString OP_enabled = UniqueString.uniqueStringOf("ENABLED");
  public static final UniqueString OP_unchanged = UniqueString.uniqueStringOf("UNCHANGED");

  /* Infix operators */
  public static final UniqueString OP_eq = UniqueString.uniqueStringOf("=");
  public static final UniqueString OP_land = UniqueString.uniqueStringOf("\\land");
  public static final UniqueString OP_lor = UniqueString.uniqueStringOf("\\lor");
  public static final UniqueString OP_implies = UniqueString.uniqueStringOf("=>");
  public static final UniqueString OP_cdot = UniqueString.uniqueStringOf("\\cdot");
  public static final UniqueString OP_equiv = UniqueString.uniqueStringOf("\\equiv");
  public static final UniqueString OP_leadto = UniqueString.uniqueStringOf("~>");
  public static final UniqueString OP_arrow = UniqueString.uniqueStringOf("-+->");
  public static final UniqueString OP_noteq = UniqueString.uniqueStringOf("/=");
  public static final UniqueString OP_subseteq = UniqueString.uniqueStringOf("\\subseteq");
  public static final UniqueString OP_in = UniqueString.uniqueStringOf("\\in");
  public static final UniqueString OP_notin = UniqueString.uniqueStringOf("\\notin");
  public static final UniqueString OP_setdiff = UniqueString.uniqueStringOf("\\");
  public static final UniqueString OP_cap = UniqueString.uniqueStringOf("\\intersect");
  public static final UniqueString OP_cup = UniqueString.uniqueStringOf("\\union");

  /* Below are not built-in operators,  but are useful definitions. */
  public static final UniqueString OP_dotdot = UniqueString.uniqueStringOf("..");	 
  public static final UniqueString OP_plus = UniqueString.uniqueStringOf("+");
  public static final UniqueString OP_minus = UniqueString.uniqueStringOf("-");
  public static final UniqueString OP_times = UniqueString.uniqueStringOf("*");
  public static final UniqueString OP_lt = UniqueString.uniqueStringOf("<");
  public static final UniqueString OP_leq = UniqueString.uniqueStringOf("\\leq");
  public static final UniqueString OP_gt = UniqueString.uniqueStringOf(">");    
  public static final UniqueString OP_geq = UniqueString.uniqueStringOf("\\geq");
  
  /* Postfix operators */
  public static final UniqueString OP_prime = UniqueString.uniqueStringOf("'");

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
