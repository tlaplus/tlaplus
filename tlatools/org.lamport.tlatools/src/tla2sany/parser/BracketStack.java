// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Fri  2 Mar 2007 at 15:32:46 PST by lamport

package tla2sany.parser;

import java.util.Stack;

import tla2sany.st.SyntaxTreeConstants;
// import tla2sany.error.*;
/***************************************************************************
* Use of classes from tla2sany/error eliminated by LL on 2 Mar 2007        *
* The only such use was of Log.log, which did logging for error tracing    *
* that was abandoned, and an "implements LogCategories".                   *
***************************************************************************/

public class BracketStack implements //LogCategories, 
                               SyntaxTreeConstants {

/***************************************************************************
* Implements a stack of StackElement objects, which have just a Kind       *
* and an Offset field, which are of type int.  The constructor is          *
* StackElement(int Offset, int Kind)                                       *
***************************************************************************/
  private Stack<StackElement> stack = new Stack<StackElement>( );
  private int [] classes = new int[ NULL_ID ];
    /***********************************************************************
    * This is an array of length NULL_ID = 227.  Apparently, NULL_ID is    *
    * an integer greater than the maximum `kind' field of any token, so    *
    * classes seems to be indexed by a token kind.  The array is           *
    * initialized at the beginning of the parse() method, so that it       *
    * defines classes[n] to equal null except for                          *
    *                                                                      *
    *   classes[BAND]   = 1                                                *
    *   classes[AND]    = 1                                                *
    *   classes[BOR]    = 2                                                *
    *   classes[OR]     = 2                                                *
    *   classes[PROOF]  = 3                                                *
    *   classes[LBR]    = 4                                                *
    *   classes[ASSUME] = 5                                                *
    *                                                                      *
    * Where BAND, ... , are the kind field values for the following        *
    * tokens                                                               *
    *                                                                      *
    *   BAND  : something like foo./\                                      *
    *   AND   : /\                                                         *
    *   BOR   :  something like foo.\/                                     *
    *   OR    :  \/                                                        *
    *   PROOF : PROOF or Proof                                             *
    *   LBR   :   (                                                        *
    *   ASSUME: ASSUME                                                     *
    *                                                                      *
    * The purpose of classes seems to be to act as a pseudo-kind field     *
    * for tokens so that BAND and AND have the same pseudo-kind, as do     *
    * BOR and OR.                                                          *
    ***********************************************************************/
    
  private int classIndex = 0;

  /*************************************************************************
  * The following three methods seem to be used only to create a single    *
  * BracketStack object and initialize its classes field.                  *
  *************************************************************************/
  public void newClass() { classIndex++; }
  public void registerInCurrentClass( int k ) {
    if ( classIndex == 0) classIndex++;
    classes[k] = classIndex;
  }

  BracketStack() {
    stack.push(new StackElement(0, -1 )) ;
  }

  void newReference( int o, int kind ) {
    /***********************************************************************
    * Puts on the top of a the stack a new StackElement object with        *
    * offset o and Kind classes[kind].                                     *
    ***********************************************************************/
     stack.push( new StackElement( o, classes[ kind ] )) ;
  }

   void popReference( ) {
     /**********************************************************************
     * Pops the top element off the stack.                                 *
     **********************************************************************/
     stack.pop();
  }

  /**
   * Returns true if the given token start column and kind match the current
   * jlist alignment and type (conjunction or disjunction).
   * 
   * @param column The token start column. 
   * @param kind The token kind (conjunction or disjunction bullet).
   * @return True if given token matches current jlist.
   */
  boolean onReference(int column, int kind) {
    StackElement current = this.stack.peek();
    return current.Offset == column && current.Kind == this.classes[kind];
  }

  /**
   * Returns true if the given token start column is to the right of the
   * current jlist alignment.
   * 
   * @param column The start column of some token.
   * @return True if strictly greater than current jlist alignment.
   */
  boolean aboveReference(int column) {
    return this.stack.peek().Offset < column;
  }
}
