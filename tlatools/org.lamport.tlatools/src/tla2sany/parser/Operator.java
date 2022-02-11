// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;
// Last modified onFri  2 Mar 2007 at 15:40:00 PST by lamport

// import tla2sany.error.*;
/***************************************************************************
* Unused import eliminated by LL on 2 Mar 2007                             *
***************************************************************************/

import util.UniqueString;

public class Operator implements tla2sany.st.SyntaxTreeConstants {

  private String Id;
  private int Low;
  private int High;
  public int Associativity;
  public int Fix;

  private static Operator voidOperator = null;
  
  // SZ Apr 16, 2009: changed to a method in order to avoid the usage
  // of the unique string in the class loading time 
  public synchronized static Operator VoidOperator()
  {  
      if (voidOperator == null)
          voidOperator = new Operator("$$_void", 0, 0, Operators.assocNone, Operators.infix);
      return voidOperator;
  }

  public Operator(String id, int l, int h, int a, int f) {
    Id = id; Low = l; High = h; Associativity = a; Fix = f;
  }
  /** @deprecated */
  public Operator(UniqueString id, int l, int h, int a, int f) {
    this(id.toString(),l,h,a,f);
  }

  // TODO appears to be unused
  /** @deprecated */
  public Operator clone ( UniqueString name ) {
    return new Operator( name, Low, High, Associativity, Fix);
  }

  public String toString() {
  switch ( Fix ) {
    case 0 /* Operators.nofix   */ : return Id + ", nofix";
    case 1 /* Operators.prefix  */ : return Id + ", prefix";
    case 2 /* Operators.postfix */ : return Id + ", postfix";
    case 3 /* Operators.infix   */ : return Id + ", infix";
    case 4 /* Operators.nfix    */ : return Id + ", nfix";
  }
  return null;
}

  public final boolean isPrefix() {
    return (Fix==Operators.prefix);
  }

  public final boolean isInfix() {
    return ( Fix == Operators.infix || Fix == Operators.nfix );
  }

  public final boolean isPostfix() {
    return ( Fix == Operators.postfix );
  }

  public final boolean isNfix() {
    return Fix == Operators.nfix ;
  }

  public final boolean isPrefixDecl() {
    return ( Fix == Operators.prefix && Id.toString().endsWith(".") );
  }

  public final boolean assocLeft() {
    return Associativity == Operators.assocLeft;
  }

  public final boolean assocRight() {
    return Associativity == Operators.assocRight;
  }

/*
(* Note that we can view a prefix or postfix operator as an infix          *)
(* operator with one empty argument.)  We can eliminate the side           *)
(* conditions by defining op1 \prec op2 to be true if op2 is not a postfix *)
(* or infix operator, and defining op2 \succ op1 to be true if op2 is not  *)
(* a prefix or infix operator.                                             *)
*/

  static final boolean succ( Operator left, Operator right) {
      return left.Low > right.High;
  }

  static final boolean prec( Operator left, Operator right ) {
    return left.High < right.Low;
  }

  static final boolean samePrec( Operator left, Operator right ) {
    return ( (left.High == right.High) && (left.Low == right.Low) );
  }

  /**
   * @deprecated
   */
  public final UniqueString getUS() {
    return UniqueString.uniqueStringOf(Id);
  }
  
  public final String getIdentifier() {
	return Id;
  }
}
