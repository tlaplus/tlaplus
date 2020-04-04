// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;

import tla2sany.utilities.Vector;
import util.UniqueString;

/***************************************************************************
* An OperatorStack object is a stack of stacks of OSelement objects.       *
***************************************************************************/

public class OperatorStack implements tla2sany.st.SyntaxTreeConstants {

  private Vector StackOfStack = new Vector (10);
    /***********************************************************************
    * The actual OperatorStack object.  It appears to be a vector of       *
    * vectors of OSElement objects.  A stack appears to be represented by  *
    * a vector v where v.elementAt(v.size()-1) is the top element of the   *
    * stack.                                                               *
    ***********************************************************************/

  private SyntaxTreeNode VoidSTNode = new SyntaxTreeNode( );

  private Vector CurrentTop = null;
    /***********************************************************************
    * Appears to be the stack of OSelement objects at the top of the       *
    * OperatorStack.  It equals null if OperatorStack is empty.  Does it   *
    * equal null only if OperatorStack is empty?  J-Ch says yes.           *
    ***********************************************************************/
    
  private ParseErrors PErrors;

  private Operator fcnOp;
    /***********************************************************************
    * This is a constant set when the OperatorStack object is created to   *
    * the operator entry for "[", which apparently is a dummy operator     *
    * representing function application.                                   *
    ***********************************************************************/
    
  public OperatorStack( ParseErrors pe ) {
    PErrors = pe;
    fcnOp = Operators.getOperator( UniqueString.uniqueStringOf("[") ); }

// could be optimized to reuse memory
  public final void newStack() {
    /***********************************************************************
    * Adds an empty stack to the top of the OperatorStack.                 *
    ***********************************************************************/
    CurrentTop = new Vector( 20 );
    StackOfStack.addElement( CurrentTop );
  }

// could be optimized to reuse memory
  public final void popStack() {
    /***********************************************************************
    * Removes the element at the top of the operator stack.                *
    ***********************************************************************/
    StackOfStack.removeElementAt( StackOfStack.size()-1 );
    if (StackOfStack.size() > 0 )
      CurrentTop = (Vector) StackOfStack.elementAt( StackOfStack.size() - 1 );
    else
      CurrentTop = null;
  }

//
  public final boolean empty() {
    return CurrentTop.size()==0; // CurrentTop 
  }

  public final int size() {
    return CurrentTop.size();
  }

/*
  We use the prec and succ relations, as described in the formal specs of the grammar.
  Their definition is embedded in the Operator class.
  One way to look at prec and succ is in term of their effect on the stack:
  if left \prec right, then shift; if left \succ right, then reduce.
                            ^^^^^
What do left and right mean?????? What does shift mean????????
  There are caveats in the case of prefix or postfix operators.
*/

// returns true if the top of the stack holds a prefix or infix op
// used to distinguish [] from [] - or vice versa ?
// also used to distinguish junction from \/ or /\
  final public boolean preInEmptyTop() {
    /***********************************************************************
    * Returns true iff OperatorStack is empty, the stack at the top of     *
    * OperatorStack is empty, or OSElement at the top of the stack at the  *
    * top of OperatorStack is that of a prefix or infix operator.          *
    ***********************************************************************/
    if (CurrentTop == null) return true; // empty or holding nothing - lookahead compliant
    if (CurrentTop.size() == 0)
      return true;
    else {
      Operator op  = ((OSelement) CurrentTop.elementAt( CurrentTop.size()-1 )).getOperator();
      if (op != null)
        return op.isPrefix() || op.isInfix();
      else
        return false;
    }
  }

  final private void reduceInfix( Operator op ) {
    /***********************************************************************
    * IF Len(CurrentTop) < 4                                               *
    *   THEN do nothing.                                                   *
    *   ELSE Suppose CurrentTop = <<head, op1, op2, op3>> \o rest          *
    *        and LET rightOp  == op1.node                                  *
    *                opNode   == op2.node                                  *
    *                leftNode == op3.node                                  *
    *        Set CurrentTop to <<head, OSelement(lSTN)>> \o rest, where    *
    *        lSTN = IF op represents an operator of type/kind N_Times      *
    *                 THEN IF leftOp is an operator of type/kind N_Times   *
    *                        THEN A node of type N_Times with heirs        *
    *                             leftOp.heirs \o <<opNode, rightNode>>    *
    *                        ELSE a node of type N_Times with heirs        *
    *                             <<leftOp, opNode, rightOp>>              *
    *                 ELSE a node of type N_InfixExpr with heirs           *
    *                      <<leftOp, opNode, rightOp>>                     *
    ***********************************************************************/
// System.err.println("infix reduction on " + op.toString() );
    int n = CurrentTop.size()-1;
//    SyntaxTreeNode localTN = new InfixExprNode();
    if (n>=3) {
      SyntaxTreeNode opNode  = ((OSelement) CurrentTop.elementAt( n-2)).getNode();
      SyntaxTreeNode leftOp  = ((OSelement) CurrentTop.elementAt( n-3)).getNode();
      SyntaxTreeNode rightOp = ((OSelement) CurrentTop.elementAt( n-1)).getNode();
      CurrentTop.removeElementAt(n-1);
      CurrentTop.removeElementAt(n-2);
      SyntaxTreeNode lSTN;

      if (op.isNfix() && leftOp.isKind( N_Times ) ) {
        SyntaxTreeNode children[] = (SyntaxTreeNode[])leftOp.heirs();
        SyntaxTreeNode newC[] = new SyntaxTreeNode[ children.length + 2];
        System.arraycopy(children, 0, newC, 0, children.length);
        newC[ newC.length-2 ] = opNode;
        newC[ newC.length-1 ] = rightOp;
        lSTN = new SyntaxTreeNode( N_Times, newC );
      } else if (op.isNfix()) { // first \X encountered
        lSTN = new SyntaxTreeNode(N_Times, leftOp , opNode, rightOp );
      } else { // inFix
        lSTN = new SyntaxTreeNode(N_InfixExpr, leftOp , opNode, rightOp );
      }
      CurrentTop.setElementAt(new OSelement(lSTN), n-3);
    }
  }

  final private void reducePrefix() {
    /***********************************************************************
    * IF Len(CurrentTop) < 3                                               *
    *   THEN do nothing                                                    *
    *   ELSE suppose CurrentTop = <<head, next, third>> \o rest            *
    *        LET opNode == third.node                                      *
    *        Set CurrentTop to <<head, OSelement(lSTN)>> \o rest, where    *
    *        lSTN is a node of kind N_PrefixExpr with heirs                *
    *             third, next.                                             *
    ***********************************************************************/
// Log.log(evalStackLog, "--- reduce prefix");
// System.out.print("prefix reduction ");
    int n = CurrentTop.size()-1;
//    SyntaxTreeNode localTN = new PrefixExprNode();
    if (n>=2) {
      Operator op = ((OSelement) CurrentTop.elementAt( n-2)).getOperator();
        /*******************************************************************
        * It appears that op is no longer used.                            *
        *******************************************************************/
      SyntaxTreeNode opNode = ((OSelement) CurrentTop.elementAt( n-2)).getNode();
// System.out.println( op.getIdentifier() );
//      if ( op.isInfix() )
//        ((GenOpNode)opNode).register( op.getIdentifier() + ".", STable);
//      else
//        ((GenOpNode)opNode).register( op.getIdentifier(), STable);
        SyntaxTreeNode lSTN = new SyntaxTreeNode(N_PrefixExpr,
          ((OSelement) CurrentTop.elementAt( n-2)).getNode(),
          ((OSelement) CurrentTop.elementAt( n-1)).getNode());
//      localTN.addChild( ((OSelement) CurrentTop.elementAt( n-2)).getNode() ) ;
//      localTN.addChild( ((OSelement) CurrentTop.elementAt( n-1)).getNode() ) ;
      CurrentTop.removeElementAt(n-1);
      CurrentTop.setElementAt(new OSelement(lSTN) , n-2);
    }
  }

  final private void reducePostfix() {
    /***********************************************************************
    * IF Len(CurrentTop) < 3                                               *
    *   THEN do nothing                                                    *
    *   ELSE suppose CurrentTop = <<head, next, third>> \o rest            *
    *        LET op     == next.op                                         *
    *            opNode == next.node                                       *
    *        Set CurrentTop to <<head, OSelement(lSTN)>> \o rest, where    *
    *        lSTN = IF op = fcnOp                                          *
    *                 THEN a node of kind N_FcnAppl with heirs             *
    *                      third.node \o opNode.heirs                      *
    *                 ELSE a node of kind N_PostfixExpr with heirs         *
    *                      third.node, opNode.                             *
    ***********************************************************************/
// Log.log(evalStackLog, "--- reduce postfix");
// System.out.println("postfix reduction");
    int n = CurrentTop.size()-1;
    SyntaxTreeNode lSTN;
//    SyntaxTreeNode localTN = new PostfixExprNode();
    if (n>=2) {
      Operator op = ((OSelement) CurrentTop.elementAt( n-1)).getOperator();
      SyntaxTreeNode opNode = ((OSelement) CurrentTop.elementAt( n-1)).getNode();
      if (op != fcnOp ) {
//      ((GenOpNode)opNode).register( op.getIdentifier(), STable);
        lSTN = new SyntaxTreeNode(N_PostfixExpr,
          ((OSelement) CurrentTop.elementAt( n-2)).getNode(),
          opNode);
//      localTN.addChild( ((OSelement) CurrentTop.elementAt( n-2)).getNode() ) ;
//      localTN.addChild( opNode ) ;
      } else {
// System.out.println("postfix reduction : FcnOp");
        SyntaxTreeNode eSTN = ((OSelement) CurrentTop.elementAt( n-2)).getNode();
        lSTN = new SyntaxTreeNode( eSTN.getFN(), N_FcnAppl, eSTN, (SyntaxTreeNode[]) (opNode.heirs()) );
      }
      CurrentTop.removeElementAt(n-1);
      CurrentTop.setElementAt(new OSelement(lSTN) , n-2);
    }
  }


// we follow case by case the definitions here.
// returns true if reduction succeeded, or was without effect.
  final public void reduceStack () throws ParseException {
    int n;
      /*********************************************************************
      * I presume java initializes n to 0                                  *
      *********************************************************************/
    Operator oR, oL;    // left and right operator
    Operator LastOp = null; // used to remember what we last reduced
    OSelement tm0, tm1, tm2;
    int a1, a2;

    do { // until (n != CurrentTop.size()-1);
      n = CurrentTop.size()-1; 
         // note !!! n is used as index, not size. XXX lousy identifier.
      tm0 = (OSelement)CurrentTop.elementAt( n );

      if ( ! tm0.isOperator() ) break; /* break = return here */
      oR = tm0.getOperator();
// System.out.println("tm0 est " + oR.toString() + printStack() );
      if ( oR.isPostfix() ) {
        if ( n == 0 ) {
          throw new ParseException("\n  Encountered postfix op " + 
                                   oR.getIdentifier() + " in block " + 
                                   tm0.getNode().getLocation().toString() + 
                                   " on empty stack");
        } else {
          tm1 = (OSelement)CurrentTop.elementAt( n-1 );
          if ( tm1.isOperator()) {
            oL = tm1.getOperator();
// System.out.println("tm1 est " + oL.toString() );
            if ( oL.isInfix() || oL.isPrefix() ) {
              throw new ParseException("\n  Encountered postfix op " + 
                                       oR.getIdentifier() + " in block " + 
                                       tm0.getNode().getLocation().toString() + 
                                       " following prefix or infix op " + 
                                       oL.getIdentifier() + ".");
            } else { // isPostfixOp - must reduce.
              reducePostfix();
            }
          } else { // tm1 is Expression - what's below ?
            if ( n > 1 ) {
              tm2 = (OSelement)CurrentTop.elementAt( n-2 );
              if ( tm2.isOperator() ) { 
                oL = tm2.getOperator();
                if ( Operator.succ( oL, oR ) ) { // prefix or infix ?
                   if ( oL.isInfix() ) reduceInfix( oL ); else reducePrefix();
                } else if ( ! Operator.prec( oL, oR ) ) {
                  throw new ParseException(
                           "Precedence conflict between ops " + 
                           oL.getIdentifier() + " in block " + 
                           tm0.getNode().getLocation().toString() + " and " 
                           + oR.getIdentifier() + ".");
		} else
		  break;
              } else {
                throw new ParseException(
                  "Expression at location " + 
                  tm2.getNode().getLocation().toString() +
                  " and expression at location " + 
                  tm1.getNode().getLocation().toString() +
                  " follow each other without any intervening operator.");
              }
            } else
              break; // nothing this time around.
          }
        }
      } else if ( oR.isPrefix() ) {
        if ( n == 0 ) break; // can't do anything yet
        else {
          tm1 = (OSelement)CurrentTop.elementAt( n-1 );
          if ( tm1.isOperator()) { // prefix, or infix
            oL = tm1.getOperator();
            if ( oL.isPostfix() ) {
              throw new ParseException(
                      "\n  Encountered prefix op " + oR.getIdentifier() + 
                      " in block " + tm0.getNode().getLocation().toString() + 
                      " following postfix op " + oL.getIdentifier() + ".");
            } else // nothing to do
              break;
          } else { // can't be expression 
            throw new ParseException(
                          "\n  Encountered prefix op " + oR.getIdentifier() + 
                          " in block " + 
                          tm0.getNode().getLocation().toString() + 
                          " following an expression.");
          }
        }
      } else { // oR.isInfix()
        if ( n == 0 ) {
            Operator mixR  = Operators.getMixfix( oR );
            if ( mixR == null )
              throw new ParseException(
                          "\n  Encountered infix op " + oR.getIdentifier() + 
                          " in block " + 
                          tm0.getNode().getLocation().toString() + 
                          " on empty stack.");
            else
              break;
        } else {
// System.out.println("infix case: " + oR.getIdentifier());
          tm1 = (OSelement)CurrentTop.elementAt( n-1 );
          if ( tm1.isOperator()) {
            oL = tm1.getOperator();
            if ( oL.isInfix() || oL.isPrefix() ) { 
                    // new case for mixfix XXX this is not exhaustive.
              Operator mixR  = Operators.getMixfix( oR );
              if ( mixR == null ) { // is infix
                if (oR == Operator.VoidOperator() )
                  throw new ParseException(
                         "\n  Missing expression in block " + 
                         tm1.getNode().getLocation().toString() + 
                         " following prefix or infix op " + 
                         oL.getIdentifier() + ".");
                else
                  throw new ParseException(
                              "\n  Encountered infix op " + 
                              oR.getIdentifier() + " in block " + 
                              tm1.getNode().getLocation().toString() + 
                              " following prefix or infix op " + 
                              oL.getIdentifier() + ".");
              } else if (   Operator.succ( oL, mixR ) 
                         || ( oL == mixR && oL.assocLeft() ) ) {
// System.out.println("precedence pbm detected");
                throw new ParseException(
                            "\n  Precedence conflict between ops " + 
                            oL.getIdentifier() + " in block " + 
                            tm1.getNode().getLocation().toString() + 
                            " and " + mixR.getIdentifier() + ".");
              } // else, skip
            } else // no choice
              reducePostfix();
          } else { // tm1 is Expression - what's below ?
// System.out.println("tm1 is expression");
            if ( n > 1 ) {
// System.out.println("deep stack");
              tm2 = (OSelement)CurrentTop.elementAt( n-2 );
              if ( tm2.isOperator() ) {
                oL = tm2.getOperator();
// System.out.println("tm2 is operator: " + oL.getIdentifier());
                Operator mixL = Operators.getMixfix( oL );
                if (  mixL != null && ((n==2) 
                    || 
                     ((OSelement)CurrentTop.elementAt( n-3 )).isOperator())) {
// System.out.println("identified prefix");
                  oL = mixL;
                } 
                if (  Operator.succ( oL, oR ) 
                    ||
                     ( oL == oR && oL.assocLeft() ) ) { 
                         // prefix or infix ?
// System.out.println("prefix or infix in succ oL, oR");
                   if      ( oL.isInfix() ) reduceInfix(oL);
                   else if ( oL.isPrefix() ) reducePrefix();
                   else {
                     if (   (tm2.getNode().getLocation().beginLine() < 
                                tm1.getNode().getLocation().beginLine() )
                         && (oR.getIdentifier() == 
                               UniqueString.uniqueStringOf("=") )) {
// System.out.println("Case 1");
                       throw new ParseException(
                              "\n  *** Hint *** You may have mistyped ==" + 
                              "\n  Illegal combination of operators " + 
                              oL.getIdentifier() + " in block " + 
                              tm2.getNode().getLocation().toString() + 
                              " and " + oR.getIdentifier() + ".");
		     } else if (oR == Operator.VoidOperator() ) {
// System.out.println("Case 2");
	               throw new ParseException(
                               "\n Error following expression at  " + 
                               tm2.getNode().getLocation().toString() + 
                               ", missing operator or separator.");
		     } else {
// System.out.println("Case 3");
                       throw new ParseException(
                              "\n  Illegal combination of operators " + 
                              oL.getIdentifier() + " in block " + 
                              tm2.getNode().getLocation().toString() + 
                              " and " + oR.getIdentifier() + ".");
		     }
                  }
                } else if (   !( Operator.prec( oL, oR ) 
                           || (oL==oR && oL.assocRight())) ) {
// System.out.println("prefix or infix in prec oL, oR+++ throwing exception");
                    throw new ParseException(
                            "\n  Precedence conflict between ops " + 
                            oL.getIdentifier() + " in block " + 
                            tm2.getNode().getLocation().toString() + 
                            " and " + oR.getIdentifier() + ".");
                } else {
// System.out.println("Case not handled");
                  break;
		}
              } else {
                throw new ParseException(
                        "Expression at location " + 
                        tm2.getNode().getLocation().toString() +
                        " and expression at location " + 
                        tm1.getNode().getLocation().toString() +
                        " follow each other without any " + 
                        "intervening operator.");
              }
            } else {
// System.out.println("Other case  not handled");
              break; // nothing this time around.
	    }
          }
        }
      }
    } while (n != CurrentTop.size()-1);
// System.out.println("exit at size: " + (CurrentTop.size()-1));
  }

  final public SyntaxTreeNode finalReduce() throws ParseException {

    int n=0;
    pushOnStack( null, Operator.VoidOperator() );
    reduceStack();
    if ( isWellReduced() )
      return ((OSelement) CurrentTop.elementAt(0)).getNode();
    else {
      StringBuffer msg = new StringBuffer("Couldn't properly parse expression");
      int l[];
      do {
//((OSelement)CurrentTop.elementAt(n)).getNode().printTree(new java.io.PrintWriter(System.out));  n++;
        msg.append("-- incomplete expression at ");
        msg.append( ((OSelement)CurrentTop.elementAt(n)).getNode().getLocation().toString() ) ;
        msg.append(".\n");
        n++;
      } while (n < CurrentTop.size()-1);
      PErrors.push( new ParseError( msg.toString(), "-- --" ));
      return null;
    }
  }

  public boolean isWellReduced () {
     return CurrentTop.size() == 2;
  }

  final public void pushOnStack( SyntaxTreeNode n, Operator o ) {
    /* XXX could be optimized to reuse OSelements */
    /***********************************************************************
    * Apparently, the operator argument o is null if this is not an        *
    * in/pre/postfix operator.                                             *
    ***********************************************************************/
// System.out.print("pushing");
// if ( n != null )
// System.out.print( " " + n.getImage() );
// if ( o != null )
// System.out.print(" " + o.toString() );
// System.out.println();
    CurrentTop.addElement( new OSelement( n, o) );
//    System.out.println(printStack());
  }

  public SyntaxTreeNode bottomOfStack() {
    return ((OSelement) CurrentTop.elementAt(0)).getNode();
  }

  public final void reduceRecord( SyntaxTreeNode middle, SyntaxTreeNode right ) throws ParseException {
    int index;
    OSelement oselt;
    int a1, a2;

    index = CurrentTop.size()-1;
    if (index < 0)
      throw new ParseException("\n    ``.'' has no left hand side at " + middle.getLocation().toString() + "." );
    oselt = (OSelement)CurrentTop.elementAt( index );

    if ( oselt.isOperator() ) {
      OSelement ospelt = (OSelement)CurrentTop.elementAt( index - 1 );
      if ( oselt.getOperator().isPostfix() && !ospelt.isOperator() ) {
        CurrentTop.addElement( null ); // humour reducePostfix
        reducePostfix();
        index = CurrentTop.size()-1;             // fix humoring
        CurrentTop.removeElementAt(index);
        index--;
        oselt = (OSelement)CurrentTop.elementAt( index );
      } else
        throw new ParseException("\n    ``.'' follows operator " + oselt.getNode().getLocation().toString() + "." );
    } 
    SyntaxTreeNode left = ((OSelement) CurrentTop.elementAt(index )).getNode();
    SyntaxTreeNode rcd = new SyntaxTreeNode(N_RecordComponent, left, middle, right);
    CurrentTop.setElementAt(new OSelement(rcd) , index);
}

// simple utility

  final private String printStack() {
    String str = new String( "stack dump, " + StackOfStack.size() + " levels, " + CurrentTop.size() + " in top one: ");
     for (int i = 0; i< CurrentTop.size(); i++ ) {
       SyntaxTreeNode tn = ((OSelement)CurrentTop.elementAt( i )).getNode();
       if (tn != null)
         str = str.concat(tn.getImage() + " " );
     }
   return str;     
  }

  final public OSelement topOfStack() {
    /***********************************************************************
    * Returns the top element of the top stack, or null if that stack is   *
    * empty.                                                               *
    ***********************************************************************/
    if (CurrentTop == null) {return null;} ;
    int n = CurrentTop.size() ;
    if (n == 0) {return null;} ;
    return (OSelement) CurrentTop.elementAt(n-1) ;
   }

  final public void popCurrentTop() {
    /***********************************************************************
    * Removes the element currently at the top of the CurrentTop stack.    *
    * Must not be called unless CurrentTop has at least one element.       *
    ***********************************************************************/
    CurrentTop.removeElementAt(CurrentTop.size() - 1) ;
   }
}
