// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.


package tlc2.tool;

import util.UniqueString;

public class BuiltInOPs implements ToolGlobals {

  private static int[] OpCodeTable;

  static {
    OpCodeTable = new int[200];
    
    /* Operators */
    put(OP_aa,   OPCODE_aa);
    put(OP_bc,   OPCODE_bc);
    put(OP_be,   OPCODE_be);
    put(OP_bf,   OPCODE_bf);    
    put(OP_case, OPCODE_case);
    put(OP_cp,   OPCODE_cp);
    put(OP_cl,   OPCODE_cl);
    put(OP_dl,   OPCODE_dl);
    put(OP_exc,  OPCODE_exc);
    put(OP_fa,   OPCODE_fa);
    put(OP_fc,   OPCODE_fc);
    put(OP_ite,  OPCODE_ite);
    put(OP_nrfs, OPCODE_nrfs);
    put(OP_pair, OPCODE_pair);
    put(OP_rc,   OPCODE_rc);
    put(OP_rs,   OPCODE_rs);
    put(OP_rfs,  OPCODE_rfs);
    put(OP_seq,  OPCODE_seq);
    put(OP_sa,   OPCODE_sa);
    put(OP_se,   OPCODE_se);
    put(OP_sf,   OPCODE_sf);
    put(OP_soa,  OPCODE_soa);
    put(OP_sor,  OPCODE_sor);
    put(OP_sof,  OPCODE_sof);
    put(OP_sso,  OPCODE_sso);
    put(OP_tup,  OPCODE_tup);
    put(OP_te,   OPCODE_te);
    put(OP_tf,   OPCODE_tf);
    put(OP_uc,   OPCODE_uc);
    put(OP_ue,   OPCODE_ue);
    put(OP_uf,   OPCODE_uf);
    put(OP_wf,   OPCODE_wf);

    /* Prefix operators */
    put(OP_lnot,      OPCODE_lnot);
    put(OP_subset,    OPCODE_subset);
    put(OP_union,     OPCODE_union);
    put(OP_domain,    OPCODE_domain);
    put(OP_box,       OPCODE_box);
    put(OP_diamond,   OPCODE_diamond);
    put(OP_enabled,   OPCODE_enabled);
    put(OP_unchanged, OPCODE_unchanged);
    
    /* Infix operators */
    put(OP_eq,       OPCODE_eq);
    put(OP_land,     OPCODE_land);
    put(OP_lor,      OPCODE_lor);
    put(OP_implies,  OPCODE_implies);
    put(OP_cdot,     OPCODE_cdot);
    put(OP_equiv,    OPCODE_equiv);
    put(OP_leadto,   OPCODE_leadto);
    put(OP_arrow,    OPCODE_arrow);
    put(OP_noteq,    OPCODE_noteq);
    put(OP_subseteq, OPCODE_subseteq);
    put(OP_in,       OPCODE_in);
    put(OP_notin,    OPCODE_notin);
    put(OP_setdiff,  OPCODE_setdiff);
    put(OP_cap,      OPCODE_cap);
    /***********************************************************************
    * The following added by LL on 2 Aug 2007.                             *
    ***********************************************************************/
    put(OP_nop,      OPCODE_nop);

    put(OP_cup,      OPCODE_cup);

    /* Postfix operators */
    put(OP_prime,    OPCODE_prime);
  }

  private static void put(UniqueString op, int opcode) {
    int loc = op.getTok();
    if (loc >= OpCodeTable.length) {
      int len1 = loc + 20;
      int[] OpCodeTable1 = new int[len1];
      for (int i = 0; i < OpCodeTable.length; i++) {
	OpCodeTable1[i] = OpCodeTable[i];
      }
      OpCodeTable = OpCodeTable1;
    }
    OpCodeTable[loc] = opcode;
  }
	
  /* Return the opcode for op. If it is not builtin, return 0. */
  public static int getOpCode(UniqueString op) {
    int loc = op.getTok();
    return (loc < OpCodeTable.length) ? OpCodeTable[loc] : 0;
  }

  public static int getOpCode(int loc) {
    return (loc < OpCodeTable.length) ? OpCodeTable[loc] : 0;
  }

  public static boolean isTemporal(int opcode) {
    return OPCODE_sf <= opcode && opcode <= OPCODE_diamond;
  }

  public static boolean isAction(int opcode) {
    return OPCODE_prime <= opcode && opcode <= OPCODE_cdot;
  }

}

