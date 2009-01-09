// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.math.BigDecimal;
import java.util.Hashtable;

import tla2sany.st.TreeNode;

/**
 * Describes a decimal like 1347.052.  This number is represented by the
 * values                    
 *                   
 *   long mantissa() = 1347052                  
 *   int  exponent() = -3                               
 *   BigDecimal bigVal() = null        
 *                               
 * so its value is mantissa() * 10^(exponent).  However, if the number  
 * can't be represented in this way, then bigVal() is the value as a    
 * BigDecimal and the other fields are meaningless.  
 *                             
 * If bigVal() equals null, then mantissa() is either a positive integer
 * not divisible by 10, or else it equals 0 and exponent() equals 0.
 */
public class DecimalNode extends ExprNode {

  private long       mantissa;                 
  private int        exponent;                         
  private BigDecimal bigVal = null;
  private String     image;

  // Bug: should remove trailing 0's from b ?
  public DecimalNode(String a, String b, TreeNode stn) {
    super(DecimalKind, stn);
    image = a + "." + b;
    try {
      this.mantissa = Long.parseLong( a + b );
      this.exponent = - b.length();
    }
    catch (NumberFormatException e) {
      this.bigVal = new BigDecimal( image );
    }
  }

  /**
   * Returns the mantissa of the decimal number, i.e its value after scaling
   * by a power of 10 until the fractional part is zero; e.g. the mantissa of 
   * 1.23 is 123.
   */
  public final long mantissa() { return this.mantissa; }

  /** 
   * The power of 10 which, when multiplied by the mantissa, yields the original number,
   * e.g. the exponent of 1.23 is -2.
   */
  public final int exponent() { return this.exponent; }

  /**
   * Returns the number in BigDecimal form
   */
  public final BigDecimal bigVal() { return this.bigVal; }

  /**
   * Returns the value as a string, exactly the way the user typed it--e.g.,    
   * without any normalization, removal of leading or trailing zero's, etc.                                      
   */
  public final String toString() { return this.image; }

  /* Level checking */
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
   *  toString, levelDataToString(), and walkGraph methods to implement
   *  ExploreNode interface
   */
//  public final String levelDataToString() { 
//    return "Level: "               + this.getLevel()               + "\n" +
//           "LevelParameters: "     + this.getLevelParams()         + "\n" +
//           "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
//           "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
//           "ArgLevelParams: "      + this.getArgLevelParams()      + "\n" ;
//  }
  
  /**
   * walkGraph finds all reachable nodes in the semantic graph and
   * inserts them in the Hashtable semNodesTable for use by the
   * Explorer tool.
   */
  public final void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;

    semNodesTable.put(new Integer(myUID), this);
  }

  /**
   * Displays this node as a String, implementing ExploreNode
   * interface; depth parameter is a bound on the depth of the portion
   * of the tree that is displayed.
   */
  public final String toString(int depth) {
    if (depth <= 0) return "";
    return( "\n*DecimalNode" + super.toString(depth) + "Mantissa: " 
            + mantissa + "; exponent: " + exponent 
            + "; big value: " + (bigVal != null ? bigVal.toString() : "<null>")
            + "\n; image = " + image 
          );
  }

}   
