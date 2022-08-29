// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Fri  2 Mar 2007 at 15:32:46 PST by lamport

package tla2sany.parser;

import tla2sany.st.SyntaxTreeConstants;

import java.util.ArrayDeque;

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
    private final ArrayDeque<StackElement> stack = new ArrayDeque<>();
    private final int[] classes = new int[NULL_ID];
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

    BracketStack() {
        stack.push(new StackElement(0, -1));
    }

    /*************************************************************************
     * The following three methods seem to be used only to create a single    *
     * BracketStack object and initialize its classes field.                  *
     *************************************************************************/
    public void newClass() {
        classIndex++;
    }

    public void registerInCurrentClass(final int k) {
        if (classIndex == 0) classIndex++;
        classes[k] = classIndex;
    }

    void newReference(final int o, final int kind) {
        /***********************************************************************
         * Puts on the top of a the stack a new StackElement object with        *
         * offset o and Kind classes[kind].                                     *
         ***********************************************************************/
        stack.push(new StackElement(o, classes[kind]));
    }

    void popReference() {
        /**********************************************************************
         * Pops the top element off the stack.                                 *
         **********************************************************************/
        stack.pop();
    }

    boolean onReference(final int o, final int kind) {
        /***********************************************************************
         * Returns true iff the top element se of the stack has se.Kind =       *
         * classes[kind] and se.Offset = o.  Throws an exception if             *
         * classes[kind] = null.                                                *
         ***********************************************************************/
        final StackElement se = stack.peek();
/************************************************************************
 * A use of a class from tla2sany/error eliminated by LL on 2 Mar 2007   *
 ************************************************************************/
        return
                classes[kind] == se.Kind && se.Offset == o;
    }


    boolean aboveReference(final int o) {
        final StackElement se = stack.peek();
// Log.log(bracketStackLog, "--- aboveReference, " + o + " " + se.Offset);
        /************************************************************************
         * A use of a class from tla2sany/error eliminated by LL on 2 Mar 2007   *
         ************************************************************************/
        return
                /***********************************************************************
                 * Returns true iff the Offset field of the top element on the stack    *
                 * is less than or equal to o.                                          *
                 ***********************************************************************/
                se.Offset - 1 < o; /* careful here. o is a beginning column, while
                          Offset is the end column of the token ...\/ ou .../\
                          on utilise - 1 pour comparer au de'but de la partie
                          significative du symbole.
                          De cette manire, le comportement ne change pas si
                          on utilise uniquement la forme non prafixe des
                         symboles */
    }
}
