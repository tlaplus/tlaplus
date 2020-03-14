// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS Position                                                           *
*                                                                          *
* A Position object has two fields, line and item, that identify a token   *
* in a tokenized spec object.  That is, the object                         *
*                                                                          *
*    [line |-> ln, item -> it]                                             *
*                                                                          *
* identifies item number it on line number ln.  (All numbering is from 0,  *
* a la Java.)  The Position                                                *
*                                                                          *
*    [line |-> -1, item -> 0]                                              *
*                                                                          *
* denotes a mythical token on the line preceding the spec.                 *
*                                                                          *
* A Position object has the method toToken(spec), which returns the        *
* token at that position in the tokenized spec.                            *
*                                                                          *
* Note: The toToken method causes an error if called with the token with   *
* line = -1.  It would simplify the program if, instead, it returned a     *
* dummy token with special type NOT_A_TOKEN.  This would eliminate a       *
* number of "line != -1" tests before calling this method.                 *
***************************************************************************/
package tla2tex;

public class Position
  { public int line = -1 ;
    public int item = 0  ;

    Position() { } ;

    Position(int line, int item) 
      {this.line = line ;
       this.item = item ;
      };

    public Token toToken(Token[][] spec)
      { Debug.Assert(   (line < spec.length) 
                     && (line >= 0) 
                     && (item < spec[line].length),
                     "toToken method of Position called with bad object");
        return spec[line][item];
      };

    public boolean equals(Position pos) {
          return (this.line == pos.line) && (this.item == pos.item) ; 
      }


    public String toString()     
      /*********************************************************************
      * Represents a Position as a (line, item) pair.                      *
      *********************************************************************/
      { if (line == -1) 
          { return "nil" ;}
        return "(" + line + ", " + item +")" ;
      } ;
  }

/* last modified on Thu 18 Aug 2005 at 22:12:43 UT by lamport */
