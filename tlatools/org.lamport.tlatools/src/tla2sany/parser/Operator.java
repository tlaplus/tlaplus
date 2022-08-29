// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;
// Last modified onFri  2 Mar 2007 at 15:40:00 PST by lamport

// import tla2sany.error.*;
/***************************************************************************
 * Unused import eliminated by LL on 2 Mar 2007                             *
 ***************************************************************************/

import util.UniqueString;

public class Operator implements tla2sany.st.SyntaxTreeConstants {

    private static Operator voidOperator = null;
    public final int Associativity;
    public final int Fix;
    private final UniqueString Id;
    private final int Low;
    private final int High;

    public Operator(final UniqueString id, final int l, final int h, final int a, final int f) {
        Id = id;
        Low = l;
        High = h;
        Associativity = a;
        Fix = f;
    }

    // SZ Apr 16, 2009: changed to a method in order to avoid the usage
    // of the unique string in the class loading time
    public static synchronized Operator VoidOperator() {
        if (voidOperator == null) {
            voidOperator = new Operator(UniqueString.uniqueStringOf("$$_void"), 0, 0,
                    Operators.assocNone, Operators.infix);
        }
        return voidOperator;
    }

    static boolean succ(final Operator left, final Operator right) {
        return left.Low > right.High;
    }

    static boolean prec(final Operator left, final Operator right) {
        return left.High < right.Low;
    }

    static boolean samePrec(final Operator left, final Operator right) {
        return ((left.High == right.High) && (left.Low == right.Low));
    }

    public Operator clone(final UniqueString name) {
        return new Operator(name, Low, High, Associativity, Fix);
    }

    public String toString() {
        return switch (Fix) {
            case 0 /* Operators.nofix   */ -> Id.toString() + ", nofix";
            case 1 /* Operators.prefix  */ -> Id.toString() + ", prefix";
            case 2 /* Operators.postfix */ -> Id.toString() + ", postfix";
            case 3 /* Operators.infix   */ -> Id.toString() + ", infix";
            case 4 /* Operators.nfix    */ -> Id.toString() + ", nfix";
            default -> null;
        };
    }

    public final boolean isPrefix() {
        return (Fix == Operators.prefix);
    }

    public final boolean isInfix() {
        return (Fix == Operators.infix || Fix == Operators.nfix);
    }

    public final boolean isPostfix() {
        return (Fix == Operators.postfix);
    }

    public final boolean isNfix() {
        return Fix == Operators.nfix;
    }

/*
(* Note that we can view a prefix or postfix operator as an infix          *)
(* operator with one empty argument.)  We can eliminate the side           *)
(* conditions by defining op1 \prec op2 to be true if op2 is not a postfix *)
(* or infix operator, and defining op2 \succ op1 to be true if op2 is not  *)
(* a prefix or infix operator.                                             *)
*/

    public final boolean isPrefixDecl() {
        return (Fix == Operators.prefix && Id.toString().endsWith("."));
    }

    public final boolean assocLeft() {
        return Associativity == Operators.assocLeft;
    }

    public final boolean assocRight() {
        return Associativity == Operators.assocRight;
    }

    public final UniqueString getIdentifier() {
        return Id;
    }
}
