// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.math.BigInteger;
import java.util.Hashtable;

import tla2sany.st.TreeNode;

/**
 * Describes a numeral like 4095.  This number is represented by the     
 * values           
 *                
 *   int val()          = 4095         
 *   BigInteger bigVal() = null            
 *               
 * However, if the number is too big to be represented as an
 * integer, then its value is bigVal() and the value of val() is
 * meaningless.   
 */
public class NumeralNode extends ExprNode {

  private int value;
  private BigInteger bigValue = null;
  private String image;

  public NumeralNode( String s, TreeNode stn ) {
    super(NumeralKind, stn);
    this.image = s;
    try {
      this.value = Integer.parseInt( s );
    } catch ( NumberFormatException e ) {
      this.bigValue = new BigInteger( s );
    }
  }

  public final int val() { return this.value; }

  public final BigInteger bigVal() { return this.bigValue; }

  /**
   * Returns the value as a string--for example, "4095".  This string
   * reflects how the value appeared in the input, so it should be
   * "\O7777" if that's what appears in the source.
   */
  public final String toString() { return this.image; }

  /* Level Checking */
  public final boolean levelCheck(int iter) {
    levelChecked = iter; 
      /*********************************************************************
      * Set it just to show that levelCHeck was called.                    *
      *********************************************************************/
    return true;
  }

//  public final int getLevel() { return ConstantLevel; }
//
//  public final HashSet getLevelParams() { return EmptySet; }
//
//  public final SetOfLevelConstraints getLevelConstraints() {
//    return EmptyLC;
//  }
//
//  public final SetOfArgLevelConstraints getArgLevelConstraints() {
//    return EmptyALC;
//  }
//
//  public final HashSet getArgLevelParams() { return EmptySet; }

  /**
   * toString, levelDataToString, and walkGraph methods to implement
   * ExploreNode interface
   */
//  public final String levelDataToString() { 
//    return "Level: "               + this.getLevel()               + "\n" +
//           "LevelParameters: "     + this.getLevelParams()         + "\n" +
//           "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
//           "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
//           "ArgLevelParams: "      + this.getArgLevelParams()      + "\n" ;
//  }

  public final void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;

    semNodesTable.put(new Integer(myUID), this);
  }

  public final String toString(int depth) {
    if (depth <= 0) return "";

    return("\n*NumeralNode: " + super.toString(depth) + " Value: " + value +
	   (bigValue != null ? ("; big value: " + bigValue.toString()) : "") +
	   "; image: " + image);
  }

}

