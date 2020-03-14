// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// Last modified on Mon 16 February 2009 at 10:05:22 PST by lamport
/***************************************************************************
* 2 Mar 2007: enum <- Enum                                                 *
***************************************************************************/

package tla2sany.semantic;

import java.util.HashMap;

import util.WrongInvocationException;

public class BuiltInLevel implements LevelConstants {

  /** 
   * The builtInLevelData array of strings contains level data for
   * each built-in operator in the language. When the arity of an
   * operator is -1, then the argWeight and argMaxLevel are just
   * at the top parenthetical level.
   */
  static class Data {
    int arity;
    int opLevel;
    int[] argMaxLevels;
    int[] argWeights;

    Data(int arity, int opLevel, int[] argMaxLevels, int[] argWeights) {
      this.arity = arity;
      this.opLevel = opLevel;
      this.argMaxLevels = argMaxLevels;
      this.argWeights = argWeights;
    }
  }
    
  private static HashMap LevelData = new HashMap();

  static int[] make() { return new int[0]; }

  static int[] make(int x) {
    int[] res = { x };
    return res;
  }

  static int[] make(int x, int y) {
    int[] res = { x, y };
    return res;
  }

  static int[] make(int x, int y, int z) {
    int[] res = { x, y, z };
    return res;
  }

  static Data data(int arity, int opLevel, int[] argMaxLevels, int[] argWeights) {
    return new Data(arity, opLevel, argMaxLevels, argWeights);
  }
  
  static {
    //                                       arity  opLevel  argMaxLevels   argWeights
    LevelData.put("STRING",               data(0,     0,       make(),       make()));
    LevelData.put("FALSE",                data(0,     0,       make(),       make()));
    LevelData.put("TRUE",                 data(0,     0,       make(),       make()));
    LevelData.put("BOOLEAN",              data(0,     0,       make(),       make()));
    LevelData.put("=",                    data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("/=",                   data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("'",                    data(1,     2,       make(1),      make(0)));
    LevelData.put("\\lnot",               data(1,     0,       make(3),      make(1)));
    LevelData.put("\\land",               data(2,     0,       make(3,3),    make(1,1)));
    LevelData.put("\\lor",                data(2,     0,       make(3,3),    make(1,1)));
    LevelData.put("\\equiv",              data(2,     0,       make(3,3),    make(1,1)));
    LevelData.put("=>",                   data(2,     0,       make(3,3),    make(1,1)));
    LevelData.put("SUBSET",               data(1,     0,       make(2),      make(1)));
    LevelData.put("UNION",                data(1,     0,       make(2),      make(1)));
    LevelData.put("DOMAIN",               data(1,     0,       make(2),      make(1)));
    LevelData.put("\\subseteq",           data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("\\in",                 data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("\\notin",              data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("\\",                   data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("\\intersect",          data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("\\union",              data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("\\times",              data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("~>",                   data(2,     3,       make(3,3),    make(0,0)));
    LevelData.put("[]",                   data(1,     3,       make(3),      make(0)));
    LevelData.put("<>",                   data(1,     3,       make(3),      make(0)));
    LevelData.put("ENABLED",              data(1,     1,       make(2),      make(0)));
    LevelData.put("UNCHANGED",            data(1,     2,       make(1),      make(0)));
    LevelData.put("\\cdot",               data(2,     2,       make(2,2),    make(0,0)));
    LevelData.put("-+->",                 data(2,     3,       make(3,3),    make(0,0)));
    LevelData.put("$AngleAct",            data(2,     2,       make(2,1),    make(0,0)));
    LevelData.put("$BoundedChoose",       data(-1,    0,       make(2),      make(1)));
    LevelData.put("$BoundedExists",       data(-1,    0,       make(3),      make(1)));
    LevelData.put("$BoundedForall",       data(-1,    0,       make(3),      make(1)));
    LevelData.put("$CartesianProd",       data(-1,    0,       make(2),      make(1)));
    LevelData.put("$Case",                data(-1,    0,       make(3),      make(1)));
    LevelData.put("$ConjList",            data(-1,    0,       make(3),      make(1)));    
    LevelData.put("$DisjList",            data(-1,    0,       make(3),      make(1)));
    LevelData.put("$Except",              data(-1,    0,       make(2),      make(1)));
    LevelData.put("$FcnApply",            data(2,     0,       make(2,2),    make(1,1)));
    LevelData.put("$FcnConstructor",      data(-1,    0,       make(3),      make(1)));
    LevelData.put("$IfThenElse",          data(3,     0,       make(3,3,3),  make(1,1,1)));
    LevelData.put("$NonRecursiveFcnSpec", data(1,     0,       make(3),      make(1)));
    LevelData.put("$Pair",                data(2,     0,       make(3,3),    make(1,1)));
    LevelData.put("$RcdConstructor",      data(-1,    0,       make(3),      make(1)));
    LevelData.put("$RcdSelect",           data(2,     0,       make(2,0),    make(1,1)));
    LevelData.put("$RecursiveFcnSpec",    data(1,     0,       make(3),      make(1)));
    LevelData.put("$Seq",                 data(-1,    0,       make(2),      make(1)));
    LevelData.put("$SetEnumerate",        data(-1,    0,       make(2),      make(1)));
    LevelData.put("$SetOfAll",            data(-1,    0,       make(2),      make(1)));
    LevelData.put("$SetOfFcns",           data(-1,    0,       make(2),      make(1)));
    LevelData.put("$SetOfRcds",           data(-1,    0,       make(2),      make(1)));
    LevelData.put("$SF",                  data(2,     3,       make(1,2),    make(0,0)));
    LevelData.put("$SquareAct",           data(2,     2,       make(2,1),    make(0,0)));
    LevelData.put("$SubsetOf",            data(1,     0,       make(2),      make(1)));
    LevelData.put("$TemporalExists",      data(1,     3,       make(3),      make(0)));
    LevelData.put("$TemporalForall",      data(1,     3,       make(3),      make(0)));
    LevelData.put("$TemporalWhile",       data(2,     3,       make(3,3),    make(0,0)));
    LevelData.put("$Tuple",               data(-1,    0,       make(2),      make(1)));
    LevelData.put("$UnboundedChoose",     data(1,     0,       make(2),      make(1)));
    LevelData.put("$UnboundedExists",     data(1,     0,       make(3),      make(1)));
    LevelData.put("$UnboundedForall",     data(1,     0,       make(3),      make(1)));
    LevelData.put("$WF",                  data(2,     3,       make(1,2),    make(0,0)));

    /***********************************************************************
    * The following added by LL on 2 Aug 2007.                             *
    ***********************************************************************/
    //                                       arity  opLevel  argMaxLevels   argWeights
    LevelData.put("$Nop",                 data(1,     0,       make(3),      make(1)));
    LevelData.put("$Qed",                 data(0,     0,       make(),       make()));
    LevelData.put("$Pfcase",              data(1,     0,       make(3),      make(1)));
    LevelData.put("$Have",                data(1,     0,       make(3),      make(1)));
    LevelData.put("$Take",                data(1,     0,       make(3),      make(1)));
    LevelData.put("$Pick",                data(1,     0,       make(3),      make(1)));
    LevelData.put("$Witness",             data(-1,    0,       make(2),       make(1)));

    /***********************************************************************
    * $Suffices added by LL 16 Feb 2009.                                   *
    ***********************************************************************/
    LevelData.put("$Suffices",            data(1,     0,       make(3),      make(1)));
  }   

  /**
   * Set up level data for built-in operators using LevelData.
   */
  public static void load () {
    Context gcon = Context.getGlobalContext();
    Context.ContextSymbolEnumeration Enum = gcon.getContextSymbolEnumeration();

    while (Enum.hasMoreElements()) {
      SymbolNode sn = Enum.nextElement();
      Data d = (Data)LevelData.get(sn.getName().toString());
      if (d != null) {
	OpDefNode opDef = (OpDefNode)gcon.getSymbol(sn.getName());
	if (opDef.getArity() != d.arity) {
	    throw new WrongInvocationException("Level data for " + sn.getName() + " has the wrong arity");
	}
	opDef.setBuiltinLevel(d);
      }	
    }
  }

}
