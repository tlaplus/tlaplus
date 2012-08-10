// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
//
// This is the version of FindAlignments modified to be consistent
// with the versions of TokenizeSpec, BuiltInSymbols, etc. that have
// been modified to handle PlusCal, but with no special PlusCal alignments
// added.  It is also being modified to add a special rule for 
// aligning labels -- or more precisely, aligning tokens that
// follow labels with other tokens.

/***************************************************************************
* CLASS FindAlignments                                                     *
*                                                                          *
* Contains the one public method                                           *
*                                                                          *
*    public static void FindAlignments(Token[][] spec)                     *
*                                                                          *
* that sets the aboveAlign, belowAlign, and isAlignmentPoint fields for    *
* all tokens in the tokenized spec spec--except for NULL and MULTI         *
* comment tokens, for which the aboveAlign field is set by                 *
* CommentToken.processComments.  (This method should be called after       *
* CommentToken.processComments.)                                           *
*                                                                          *
* There are six kinds of alignments, illustrated by the following          *
* example:                                                                 *
*                                                                          *
*    Alignment Type         Tokens so aligned                              *
*    --------------         -----------------                              *
*    FirstNonLeftComment   foo, x, + , /\ , y/comment r, u/comment k       *
*                                           ^^^^^^^^^^^                    *
*                                I think this should be +/comment r        *
*    LeftComment           comments j                                      *
*    CommentInner          comments p                                      *
*    InfixInner            ==, => , >                                      *
*    AfterInfixInner       m, c,                                           *
*    InfixArg              a, z/z, y/z                                     *
*                                                                          *
*             foo == LET x == /\ a  =>  m * n >  c                         *
*             |   |      | |  |  |  |   |     |  |                         *
*    (* j *)  |   |      | |  /\ a  =>  m / q >  c  (* p *)                *
*    |        |   |      | |                        |                      *
*    (* j *)  |   |      x ==   z                   |                      *
*             |   |             |                   |                      *
*             |   |           + z                   \* p                   *
*             |   |           | |                   |                      *
*             |   |           | |                   (* p *)                *
*             |   |           | |                   |                      *
*             |   |           + y                   (* p *)                *
*             |   |           |                                            *
*             |   |           \* r                                         *
*             |   |                                                        *
*             foo ==                                                       *
*              |                                                           *
*              (* k *)                                                     *
*              |                                                           *
*              u + v                                                       *
*                                                                          *
* For InfixInner and CommentInner alignment, a token's belowAlign          *
* field points to the token directly below it with which it is             *
* aligned.                                                                 *
*                                                                          *
* For all alignment types, if a token t1 is aligned with a token           *
* t2 above it, then t1.aboveAlign points to:                               *
*                                                                          *
*   IF t2 has no aboveAlign pointer THEN t2                                *
*                                   ELSE t2.abovealign.                    *
*                                                                          *
* Thus, in the example above, the aboveAlign pointer for all the p         *
* comments point to the first p comment.                                   *
*                                                                          *
* To define the types of alignment, we use the following definitions:      *
*                                                                          *
* - A LEFT-COMMENT is a comment that is the first token on its line but    *
*   not the last token on its line.  (The comments (* j *) in the          *
*   example are left-comments.)  For all the types of alignment except     *
*   CommentInner, left-comments are treated as if they didn't exist.       *
*                                                                          *
* - A RIGHT-COMMENT is a comment that is the last token on its line.       *
*                                                                          *
* Any comment other than a left-comment or a right-comment is treated      *
* like any other non-built-in token.  We also define:                      *
*                                                                          *
* - The COVERING TOKEN of a token t is the right-most token ct that        *
*   covers t on the last line (one with biggest line number) containing    *
*   a token that covers t, where a token t1 COVERS a token t2 if t1        *
*   lies on an earlier line than t2 and t1.column \leq t2.column.          *
*   However, if there is a DASH between ct and t, or                       *
*   on the same line as ct, then t has no covering token.                  *
*   (This definition has two versions, depending on whether or not         *
*   left-comments are ignored.)                                            *
*                                                                          *
* - The BLOCKING TOKEN of a token t is the left-most token s with          *
*   s.column \geq t.column on the last line before t's line containing     *
*   such a non-left-comment token s.                                       *
*                                                                          *
* Here are the descriptions of the different types of alignment.           *
*                                                                          *
*                                                                          *
* CommentInner:                                                            *
*    Token t at position pos is CommentInner above-aligned with its        *
*    blocking token bt at position bpos iff:                               *
*       /\ t is a right-comment                                            *
*       /\ bt is a right-comment                                           *
*       /\ t.column = bt.column                                            *
*       /\ \/ bt is not above-aligned with anything                        *
*          \/ bt is CommentInner aligned with a token above it             *
*                                                                          *
* FirstNonLeftComment                                                      *
*    If t is the first token on a line that is not a left-comment, and is  *
*    not a right-comment that is CommentInner aligned with a token above   *
*    it, then t is FirstNonLeftComment aligned with its covering token.    *
*                                                                          *
* LeftComment:                                                             *
*    If t is a left-comment token, then it is LeftComment aligned          *
*    with its covering token (where left-comments are visible).            *
*                                                                          *
* InfixInner:                                                              *
*    Token t at position pos is InfixInner aligned with its covering       *
*    token ct at position cpos iff t is not FirstNonLeftComment aligned,   *
*    and both t and ct are built-in symbols with the same nonzero alignment  *
*    class.  (The name InfixInner is misleading because non-infix symbols  *
*    like ":" get aligned by this mechanism.)                              *
*                                                                          *
* AfterInfixInner:                                                         *
*    Token t is After InfixInner aligned with the token above it iff       *
*                                                                          *
*       LET lt  == the token to the left of t                              *
*           alt == the token at position lt.aboveAlign                     *
*           at  == the token to the right of alt                           *
*       IN  /\ t is not the first token on the line                        *
*           /\ lt is InnerAligned with token alt above it                  *
*           /\ alt is not the last token on its line.                      *
*           /\ at is the covering token of t                               *
*           /\ t.column = at.column                                        *
*           /\ at is not a comment                                         *
*    (The name AfterInfixInner means "after InfixInner alignment".         *
*    Remember that some non-infix symbols get InfixInner aligned.)         *
*                                                                          *
* InfixArg:                                                                *
*    Token t is InfixArg aligned with its covering token ct iff:           *
*       LET lt == the token to the left of t                               *
*           alt == the token at position lt.aboveAlign                     *
*       IN  /\ t is not the first token on the line                        *
*           /\ lt is the first non-left-comment token                      *
*           /\ lt is an infix operator                                     *
*           /\ lt is not InfixInner aligned with any token above it.       *
*           /\ t.column = ct.column                                        *
*           /\ alt is the token to the left of ct                          *
*           /\ lt is either aligned with or lies entirely to the           *
*              right of alt.                                               *
*                                                                          *
*   Note: The large number of conditions are an attempt to rule            *
*   out spurious alignments.                                               *
* ----------------------------------------------------------------------   *
*                                                                          *
* PlusCal Alignment                                                        *
* -----------------                                                        *
*                                                                          *
* The following rule is added for PlusCal.                                 *
*                                                                          *
* Define a token t to be a FIRST NON-LABEL if either                       *
*     (a) it is the first token on the line, or                            *
*     (b) it is the 2nd token on its line and the first token on           *
*         the line is a label.                                             *
*                                                                          *
* AfterLabel:                                                              *
*   A token t is AfterLabel aligned with a token ta iff:                   *
*     /\ t is a first non-label that is the 2nd token on its line          *
*     /\ t and ta are left-aligned                                         *
*     /\ there is no line between t and ta containing any token            *
*        to the left of t other than a label that is the line's            *
*        first token.                                                      *
*     /\ \/ ta is a first non-label                                        *
*        \/ /\ ta is above t                                               *
*           /\ \/ ta is the first token on the line                        *
*              \/ the token to the left of ta is a label or                *
*                 a PlusCal symbol                                         *
*                                                                          *
* Here's an example of AfterLabel alignment.  Token b and all the x        *
* tokens are AfterLabel aligned with token A. Tokens A and B and all the   *
* other x tokens are also AfterLabel aligned with the first and last x     *
* tokens.                                                                  *
*                                                                          *
*            { B                                                           *
*          l:  x                                                           *
*          m:    z                                                         *
*              x                                                           *
*          l:  A                                                           *
*                z                                                         *
*              x                                                           *
*        l:    x                                                           *
*            } z                                                           *
*                                                                          *
* Note that B is the only token whose alignment is due to the second       *
* disjunction of the last conjunction.  That disjunct is designed to try   *
* to rule out bogus alignments such as the alignment of the y's with the   *
* 0 in                                                                     *
*                                                                          *
*     if (x = 0) {                                                         *
*       lab:  y := 1;                                                      *
*       lab:  y := 2  }                                                    *
*                                                                          *
* while aligning the the y's in                                            *
*                                                                          *
*      if (x = 0) {     y := 0;                                            *
*                  lab: y := 1;                                            *
*                  lab: y := 2  }                                          *
*                                                                          *           
* and in                                                                   *
*                                                                          *
*      if (x = 0) { y := 0;                                                *
*   lab:            y := 1;                                                *
*   lab:            y := 2  }                                              *
*                                                                          *
* ----------------------------------------------------------------------   *
*                                                                          *
* Note: A possible addition is a special case to recognize alignments      *
* after a comma, as in                                                     *
*                                                                          *
*        <<abcdef,  ghi + 7, jklmn>>                                       *
*                   |        |                                             *
*        <<a,       bc,      def>>                                         *
*                                                                          *
* However, that should be done only if there's a clear intention to align  *
* them--as evidenced here by the extra spaces between the "a,", the "cb,"  *
* and the "def".  Otherwise, there would be too many chance alignments.    *
***************************************************************************/
package tla2tex;

public class FindAlignments
{ public static void FindAlignments(Token[][] spec)
    { setSubscriptField(spec) ;
        /*******************************************************************
        * Set the subscript fields of the tokens.                          *
        *******************************************************************/
      int line = 0 ;
        
      /*********************************************************************
      * Skip all lines beginning with a prolog token.  This means that if  *
      * the module begins on the same line as a prolog token, then the     *
      * first line of the spec is ignored for alignment.  Tant pis!        *
      *********************************************************************/
      boolean inProlog = true ;
      while (inProlog && (line < spec.length))
       { if (    (spec[line].length > 0)
              && (spec[line][0].type != Token.PROLOG))
           { inProlog = false;}
         else
           { line = line + 1;}
       };
      
      /*********************************************************************
      * Set aboveAlign and belowAlign "pointers".                          *
      *********************************************************************/
      while (line < spec.length)
       { int item = 0 ;
         boolean prevInfixInner = false ;
           /****************************************************************
           * True iff the previous item on the line was InfixInner         *
           * aligned.                                                      *
           ****************************************************************/
         while (item < spec[line].length)
          { 
            /***************************************************************
            * Set token, pos to the current token and its position.        *
            ***************************************************************/
            Position pos = new Position(line, item) ;
            Token    token = spec[line][item] ;

            if (! token.subscript)
             {/*************************************************************
              * Do not align subscript tokens.                             *
              *************************************************************/
              if (isRightComment(spec, pos))
              { /***********************************************************
                * This is a RightComment.  First check if it should be     *
                * CommentInner aligned.  If not, check if it should be     *
                * FirstNonLeftComment aligned.                             *
                ***********************************************************/

                /***********************************************************
                * Set btoken, bpos to the blocking token of `token' and    *
                * its position.                                            *
                ***********************************************************/
                Position bpos   = blockingPosition(spec, pos);              
                Token    btoken =  null ;
                if (bpos.line != -1) {btoken = bpos.toToken(spec);};
                
                /***********************************************************
                * Set ctok to be a CommentToken alias for token.           *
                ***********************************************************/
                CommentToken ctok = (CommentToken) token ;
                if (   (ctok.subtype == CommentToken.MULTI)
                    || (ctok.subtype == CommentToken.NULL))
                 { /********************************************************
                   * This is the continuation of a multi-column comment.   *
                   ********************************************************/
                   Debug.Assert(   (btoken != null) 
                                && (btoken.type == Token.COMMENT),
                      "Bad blocking token for a MULTI or NULL token");
                   
                   /********************************************************
                   * Set token's aboveAlign to point to the BEGIN_MULTI    *
                   * token beginning the commnet.                          *
                   ********************************************************/
                   if ( ((CommentToken) btoken).subtype 
                            == CommentToken.BEGIN_MULTI)
                     { token.aboveAlign = bpos ; }
                   else
                     { token.aboveAlign = btoken.aboveAlign ; };

                   /********************************************************
                   * Make the blocking token's belowAlign pointer point    *
                   * to token.                                             *
                   ********************************************************/
                   btoken.belowAlign = pos ;
                 } // END then OF if  if ((ctok.subtype == .. ))
                else
                 { /********************************************************
                   * This is not the continuation of a multi-line          *
                   * comment.  Try to CommentInner align it.               *
                   ********************************************************/

                   if (   (bpos.line != -1)
                       && isRightComment(spec, bpos)
                       && (btoken.column == token.column)
                       && (   (   (btoken.aboveAlign.line == -1)
                               && (bpos.item > 0))
                           || (   (btoken.aboveAlign.line != -1)
                               && (btoken.aboveAlign.
                                     toToken(spec).belowAlign.line != -1))
                                /**********************************************
                                * Asserts that bpos is aboveAligned with a    *
                                * token that is belowAligned with something,  *
                                * which is possible only if bpos is           *
                                * CommentInner aligned.                       *
                                **********************************************/
                          )     
                      )
                     { /****************************************************
                       * CommentInner align.                               *
                       ****************************************************/
                       btoken.belowAlign = pos ; 
                       if (btoken.aboveAlign.line == -1)
                         { token.aboveAlign = bpos; }
                       else
                         { token.aboveAlign = btoken.aboveAlign ;};
                     }  // END then OF if ((bpos.line != -1)...)
                   else
                     { /*******************************************************
                       * FirstNonLeftComment align iff it is the first        *
                       * non-left comment.                                    *
                       *******************************************************/
                       if (   (item == 0)
                           || (   (item == 1)
                               && (spec[line][0].type == Token.COMMENT)))
                         { pos.toToken(spec).aboveAlign = 
                             coveringPosition(spec, pos, true) ;
                         } ;
                     }; // END else OF if ((bpos.line != -1)...)


                 } // END else OF if  if ((ctok.subtype == .. ))
                prevInfixInner = false ;
              } // END then OF if (isRightComment(spec, pos))                

              { /***********************************************************
                * This is not a right-comment.  Check for every kind of    *
                * alignment except CommentInner.                           *
                ***********************************************************/
                if (prevInfixInner)
                 { /********************************************************
                   * Check for AfterInfixInner alignment.                  *
                   *                                                       *
                   * In the following, the positions lPos, alPos, and      *
                   * aPos are defined by                                   *
                   *                            alPos --- aPos             *
                   *                              |                        *
                   *                              |                        *
                   *                             lPos --- pos              *
                   ********************************************************/
                   Debug.Assert(pos.item > 0, 
                      "prevInfixInner true for first item on line");
                   Position lPos  = new Position(pos.line, pos.item - 1);
                   Debug.Assert(lPos.toToken(spec).aboveAlign.line != -1,
                     "prevInfixInner true, but token to left not aligned");
                   Position alPos = lPos.toToken(spec).aboveAlign ;
                   Token alToken = alPos.toToken(spec);
                   if (alPos.item + 1 < spec[alPos.line].length)
                    { Position aPos   = 
                          new Position(alPos.line, alPos.item + 1) ;
                      Token    atoken = aPos.toToken(spec);
                      Position cPos   = coveringPosition(spec, pos, true);
                      if (   (cPos.line == aPos.line)
                          && (cPos.item == aPos.item)
                          && (token.column == atoken.column)
                          && (atoken.type != Token.COMMENT) )
                        { /*************************************************
                          * AfterInfixInner aligned.                       *
                          *************************************************/
                           token.aboveAlign = aPos;
                        } ;
                    } // END if (alPos.item + 1 < spec[alPos.line].length)
                   prevInfixInner = false;
                 } // END then OF if (prevInfixInner)
               else
                 { /********************************************************
                   * Check for every kind of alignment except              *
                   * AfterInfixInner and CommentInner.                     *
                   *                                                       *
                   * First, check if FirstNonLeftComment aligned.          *
                   ********************************************************/
                   if (   ((item == 0) && (token.type != Token.COMMENT))
                       || ((item == 1) && (spec[line][0].type 
                                              == Token.COMMENT)))
                    { /*****************************************************
                      * FirstNonLeftCommentAligned.                        *
                      *****************************************************/
                      token.aboveAlign = 
                            coveringPosition(spec, pos, true);
                    }
                   else
                    { /*****************************************************
                      * Not FirstNonLeftCommentAligned.                    *
                      *                                                    *
                      * Next, check if LeftComment aligned.                *
                      *****************************************************/
                      if (isLeftComment(spec, pos))
                        { token.aboveAlign = 
                            coveringPosition(spec, pos, false);
                        }
                      else
                        { /*************************************************
                          * Next, check if InfixInner aligned.             *
                          *************************************************/
                          Position cpos = coveringPosition(spec, pos, true) ;
                          Token ctoken = null ;
                            /***********************************************
                            * cpos and ctoken are the covering position    *
                            * and covering token of the current token.     *
                            ***********************************************/
                          if (cpos.line != -1)
                            { ctoken = cpos.toToken(spec);};
                          int alignClass = 0 ;  // The alignment classes
                          int calignClass = 0;  //   of pos and cpos.
                          if (token.type == Token.BUILTIN)
                           { alignClass = 
                                BuiltInSymbols.GetBuiltInSymbol(
                                   token.string, true).alignmentType ; } ;
                          if (   (ctoken != null)
                              && (ctoken.type == Token.BUILTIN))
                           { calignClass = 
                                BuiltInSymbols.GetBuiltInSymbol(
                                   ctoken.string, true).alignmentType ; } ;
                          if (   (ctoken != null)
                              && (token.column == ctoken.column)
                              && (alignClass != 0)
                              && (alignClass == calignClass))
                           { /**********************************************
                             * InfixInner alignment.                       *
                             **********************************************/
                             ctoken.belowAlign = pos ;
                             if (ctoken.aboveAlign.line == -1)
                              {token.aboveAlign = cpos ; }
                             else
                              { token.aboveAlign = ctoken.aboveAlign ; };
                             prevInfixInner = true;
                           }  // END then OF if ((token.column == ...))
                          else
                           { /**********************************************
                             * Not InfixInner alignment.  Check last       *
                             * possibility, which is InfixArg alignment.   *
                             **********************************************/
                             if (   (   (item == 1)
                                     || (   (item == 2)
                                         && (spec[line][0].type == 
                                               Token.COMMENT)))
                                 && (spec[line][item-1].type == Token.BUILTIN)
                                 && (BuiltInSymbols.GetBuiltInSymbol(
                                       spec[line][item-1].string, true).symbolType
                                      == Symbol.INFIX)
                                 /******************************************
                                 * Correction made 7 Nov 2001.             *
                                 * The conjunct above replaced the         *
                                 * following.                              *
                                 *                                         *
                                 * && (BuiltInSymbols.GetBuiltInSymbol(    *
                                 *       spec[line][item-1].string         *
                                 *        ).alignmentType != 0)            *
                                 *                                         *
                                 * It seems reasonable that this           *
                                 * alignment should be performed only      *
                                 * when the token to the left is an infix  *
                                 * operator.                               *
                                 ******************************************/
                                 && (ctoken != null) 
                                 && (token.column == ctoken.column)
                                 && (spec[line][item-1].aboveAlign.line
                                       != -1)
                               )
                              { /*******************************************
                                * Possible InfixArg alignment.             *
                                *******************************************/
                             // This can happen and seems harmless.
                             //   Debug.Assert(ctoken.belowAlign.line == -1,
                             //       "Trying to InfixArg align with token "
                             //   + "that is not aligned with token below it");

                                 Token lTok = spec[line][item-1] ;
                                   /****************************************
                                   * The token to the left of the current  *
                                   * token.                                *
                                   ****************************************/
                                Position alPos = lTok.aboveAlign ;
                                Token alTok = alPos.toToken(spec);
                                  /*****************************************
                                  * The token with which lTok is aligned   *
                                  * above.                                 *
                                  *****************************************/
                                if (   (alPos.line == cpos.line)
                                    && (alPos.item == cpos.item - 1)
                                    )
                                 { /****************************************
                                   * InfixArg alignment with a token       *
                                   * having a token to its left, as in     *
                                   *                                       *
                                   *   x ==   a                            *
                                   *          |                            *
                                   *        + b                            *
                                   ****************************************/
                                   token.aboveAlign = cpos; 
                                   // following fixes the mis-alignment that occurs if
                                   // the "x == " occupies less space than the "+".
                                   // However, for safety, I'm only fixing it for the
                                   // case of labels, which should be more common.
                                   // However, I'm not doing it until I find
                                   // some example of the bug for fear that it
                                   // might break something else.
                                   //
                                   //    ctoken.belowAlign = pos ;
                                 } 
                               else
                                 { if (   (cpos.item == 0)
                                       || (   (cpos.item == 1)
                                           && (spec[cpos.line][0].type 
                                                        == Token.COMMENT)))
                                    { /*****************************************
                                      * InfixArg alignment with a token        *
                                      * having no token to its left.  In       *
                                      * this case, we can have a               *
                                      * situation like                         *
                                      *                                        *
                                      *    x ==                                *
                                      *     a                                  *
                                      *   + b                                  *
                                      *                                        *
                                      * where a is both above-aligned          *
                                      * with x and below-aligned with b.       *
                                      * I hope this doesn't cause              *
                                      * problems.                              *
                                      *****************************************/
                                      token.aboveAlign = cpos;           
                                      ctoken.belowAlign = pos ;
                                    } ;
                                 }
                              };
                           };// END else OF if ((token.column == ...))
                        }; // END else of if (isLeftComment(spec, pos))
                    }; // END else OF if (   ((item == 0) && ... ))
                 }; // END else OF if (prevInfixInner)
              }; // END else OF (isRightComment(spec, pos))                   
             }   // END then OF if (! token.subscript)
            else
             { prevInfixInner = false ;
                 /**********************************************************
                 * Need to reset prevInfixInner for the tokens following   *
                 * a ^ or _.                                               *
                 **********************************************************/
             } ;  
           item = item + 1 ;
          } ; // END while (item < spec[line].length)

         line = line + 1;
         /******************************************************************
         * Skip over epilog lines.                                         *
         ******************************************************************/
         if (    (line < spec.length) 
              && (spec[line].length > 0)
              && (spec[line][0].type == Token.EPILOG))
           { line = spec.length ;} ;
       }; // END while (line < spec.length)

       // Add the AfterLabel alignments.
       FindLabelAlignments(spec) ;

       /*********************************************************************
      * Set isAlignmentPoint flags.  For simplicity, it is set true for    *
      * any token that is not the first on the line and is either the      *
      * source or target of a belowAlign pointer                           *
      *********************************************************************/
      line = 0 ;
      while (line < spec.length)
       { int item = 0 ;
         while (item < spec[line].length)
          { Token token = spec[line][item] ;
            if (token.aboveAlign.line != -1)
              { if (item > 0)
                  {token.isAlignmentPoint = true ;
                  };
                if (token.aboveAlign.item != 0)
                   /********************************************************
                   * Corrected apparent bug on 16 Jan 00: This if          *
                   * condition was: token.aboveAlign.line != 0.            *
                   ********************************************************/
                  { token.aboveAlign.toToken(spec).isAlignmentPoint 
                            = true; 
                  };
              } ;

            if (token.belowAlign.line != -1)
              { if (item > 0)
                  {token.isAlignmentPoint = true ;
                  };
                if (token.belowAlign.line != 0)
                  { token.belowAlign.toToken(spec).isAlignmentPoint 
                            = true; 
                  };
              } ;

            item = item + 1 ;
          } ; // END while (item < spec[line].length)

         line = line + 1;
       }; // END while (line < spec.length)
    } ;

  /**
   * Adds AfterLabel alignments to spec.  More precisely, for something like
   * 
   *  if (x) { stmt
   *    label: stmt
   *           stmt
   *    label: stmt
   *           stmt
   *           stmt
   *        }
   * 
   * it makes the belowAlign field of all stmts but the last one point to the
   * stmt below it, and the aboveAlign field of all but the first stmt point to
   * the one above it.  In this case
   * 
   *    while x
   *           stmt
   *    label: stmt
   * 
   * the first stmt's aboveAlign field should point to x by the FirstNonLeftComment
   * alignment rule.  For
   * 
   *    while x
   *    label: stmt
   *    label: stmt
   * 
   * the method sets the first stmt's aboveAlign field
   *  
   * @param spec
   */
  public static void FindLabelAlignments(Token[][] spec) {
      /*
       * Do nothing if there is no PlusCal algorithm.
       */
      if (!TokenizeSpec.hasPcal) {
          return ;
      }
      
      /*
       * We get the first and last line that may begin with a label or a 
       * PlusCal statement.  Since the algorithm begins with --algorithm
       * or --fair, we skip the algorithm's first line.
       */
      int pcalStartLine = TokenizeSpec.pcalStart.line + 1 ;
      int pcalEndLine   = TokenizeSpec.pcalEnd.line ;
      
      /*
       * The algorithm works by repeatedly searching for the next line beginning
       * with a label followed by a token tok.  It then performs the following
       * two steps
       * 
       * 1. Searche downward for tokens AfterLabel aligned with tok, setting
       *    aboveAlign/belowAlign fields as it finds them. It stops when it reaches a 
       *    line in which tok is not not aligned with the first token on the
       *    line.  If there's a token etok on that line that is AfterLabel
       *    aligned with tok, so it must follow a label, then the aboveAlign
       *    field of etok is set to point to the AfterLabel aligned token above
       *    it, whose belowAlign field points to etok.
       *    
       * 2. IF tok's aboveAlign field points to a token whose belowAlign field
       *       points to a field whose belowAlign field points to tok
       *     THEN do nothing.  I think this is possible only if those fields were set
       *          by step 1 for a previous label.  If I'm wrong and there's some weird
       *          situation that caused this alignment (which I think can only be
       *          the case if tok is a comment), then not stopping will probably
       *          do more harm than good.
       *     ELSE search upwards to set aboveAlign/belowAlign fields of tokens 
       *          AfterLabel aligned with tok. As indicated above, if there
       *          are no tokens above tok that are AfterLabel aligned with it,
       *          then tok's aboveAlign field must be set to point to its
       *          covering token.   
       */
      int curLabelLine = pcalStartLine ;
      
      while (   (curLabelLine <= pcalEndLine)
             && (curLabelLine < spec.length) ) {
          /* 
           * set curLabelLine to the first line at or below its current
           * position that begins with a label.
           */
          if (   (spec[curLabelLine].length > 1)
              && (spec[curLabelLine][0].type == Token.PCAL_LABEL) ) {
              
              Token tok = spec[curLabelLine][1] ;
              int alignCol = tok.column ;

              // Perform step 1 for token tok
              int curLine = curLabelLine + 1 ;
              
              // spec[alignLine][alignItem] is the token to which the
              // next token to be aligned is aligned with.
              int alignLine = curLabelLine ;
              int alignItem = 1 ;
              boolean notDone = true ;
              while (notDone) {
                  int curItem = 0 ;
                     // If spec[alignLine][alignItem] is to be aligned with a token
                     // on this line, then the token is spec[curLine][nextItem] 
                     // 
                  boolean shouldSkip = false ;
                  if (spec[curLine].length != 0) {
                      if (spec[curLine][0].type == Token.PCAL_LABEL) {
                          // line begins with label
                          if (spec[curLine].length > 1) {
                              curItem = 1 ;
                          }
                          else {
                              // The label is the only token on the line.  Stop
                              // iff the label is to the left of the alignment
                              // column.
                              notDone = (spec[curLine][0].column >= alignCol) ;
                              shouldSkip = true ;
                          }
                      }
                      else {
                          // line doesn't begin with label
                      }
                      if (!shouldSkip) {
                          if (spec[curLine][curItem].column < alignCol) {
                              notDone = false ;
                          }
                          else if (spec[curLine][curItem].column == alignCol) {
                              spec[alignLine][alignItem].belowAlign = 
                                      new Position(curLine, curItem) ;
                              spec[curLine][curItem].aboveAlign =
                                      new Position(alignLine, alignItem) ;
                              alignLine = curLine ;
                              alignItem = curItem ;
                          }
                      }
                  }
                  curLine++ ;
                  if (   (curLine > pcalEndLine)
                      || (curLine >= spec.length)) {
                      notDone = false ;
                  }
              }
              
              // Perform step 2 for token tok
              
              if (    (tok.aboveAlign.line != -1)
                   && (tok.aboveAlign.toToken(spec).belowAlign.equals(new Position(curLabelLine, 1)))) {
                  // already aligned with above tokens so do nothing
              }
              else {
                  curLine = curLabelLine - 1 ;
                  alignLine = curLabelLine ;
                  alignItem = 1 ;
                  notDone = true ;
                  while (notDone) {
                     if (   (spec[curLine].length > 0 )
                         && (spec[curLine][0].column <= alignCol)
                         && (   (spec[curLine][0].type != Token.PCAL_LABEL)
                             || (   (spec[curLine].length > 1)
                                  && (spec[curLine][1].column <= alignCol) ) )
                            // the conjunct above causes the line to be skipped
                            // if the only token to the left of tok on this
                            // line is an initial label followed by a token
                            // to the right of tok.
                        ) {
                         if (spec[curLine][0].column == alignCol) {
                             //  spec[curLine][0] is to be aligned with 
                             //  spec[alignLine][alignItem] 
                             spec[alignLine][alignItem].aboveAlign = 
                                     new Position(curLine, 0) ;
                             spec[curLine][0].belowAlign =
                                     new Position(alignLine, alignItem) ;
                             alignLine = curLine ;
                             alignItem = 0 ; 
                         }
                         else if (spec[alignLine][alignItem].aboveAlign.line == -1) {        
                             // we need to align spec[alignLine][alignItem] with the
                             // right-most token on line curLine with column \leq alignCol
                             int item = 0 ;
                             while (   (item < spec[curLine].length)
                                    && (spec[curLine][item].column <= alignCol)) {
                                 item++;
                             }
                             // item is now either off the line or pointing to a token
                             // to the right of the alignment token ;
                             item-- ;
                             
                             // We  set the aboveAlign pointer of 
                             // to point to spec[curLine][item] if the latter token is either
                             // the first one on its line, or else the token to its left is
                             // either a label or a PlusCal token.  
                             // If that's the case, we also set the belowAlign pointer of 
                             // spec[curLine][item] if that token is in the same column
                             // as spec[alignLine][alignItem].
                             // 
                             Token altok = null ;
                             if (item > 0) {
                                 altok = spec[curLine][item-1] ;
                             }
                             if (   (altok != null)
                                 && (   (altok.type == Token.PCAL_LABEL)
                                     || (   (altok.type == Token.BUILTIN)
                                         && BuiltInSymbols.IsBuiltInSymbol(altok.string, true)
                                         && ! BuiltInSymbols.IsBuiltInSymbol(altok.string, false)
                                        )
                                    )
                                ) {
                                 spec[alignLine][alignItem].aboveAlign = 
                                            new Position(curLine, item) ;
                                
                                 if (spec[curLine][item].column == alignCol) {
                                     spec[curLine][item].belowAlign =
                                             new Position(alignLine, alignItem) ;
                                 }
                             }
                             // This ends step 2
                             notDone = false ;
                         }
                         else {
                             notDone = false ;
                         }
                     }
                     curLine-- ;
                     if (curLine < pcalStartLine) {
                         notDone = false ;
                     }
                  }
              }     
          }
          curLabelLine++ ;
      }       
  }
  /*************************************************************************
  * The following are functions used in FindAlignments.                    *
  *************************************************************************/
  private static boolean isLeftComment(Token[][] spec, Position p)
    /***********************************************************************
    * A left-comment is a comment token that is the first token on a line  *
    * and has another token to its right.  This method returns true iff    *
    * the token at position p of spec is a left-comment.                   *
    ***********************************************************************/
    { return    (p.item == 0)
             && (spec[p.line][p.item].type == Token.COMMENT) 
             && (spec[p.line].length > 1) ;
    } ;

  private static boolean isRightComment(Token[][] spec, Position p)
    /***********************************************************************
    * A right-comment is a comment token that is the last token on its     *
    * line.  This method returns true iff the token at position p in spec  *
    * is a right-comment.                                                  *
    ***********************************************************************/
    { return    (p.item == spec[p.line].length - 1)
             && (spec[p.line][p.item].type == Token.COMMENT) ;
    } ;

  private static Position coveringPosition( 
                          Token[][] spec, Position p, boolean ignore)
    /***********************************************************************
    * A token t1 COVERS a token t2 if t1 lies on an earlier line than t2   *
    * and t1.column \leq t2.column.  This method searches upwards to find  *
    * the first line with a token that covers the token at position p,     *
    * and then returns the position of the right-most token on that line   *
    * that covers the token at p.  When searching for the covering token,  *
    * left-comments are ignored iff the ignore parameter is true.          *
    ***********************************************************************/
    { /*********************************************************************
      * Find covering line.                                                *
      *********************************************************************/
      int   line = p.line - 1 ;
      Token tok = p.toToken(spec) ;
      boolean notDone = true ;
      while ((line >= 0) && notDone)
       { if (spec[line].length > 0)
           { if (spec[line][0].type == Token.PROLOG)
               { line = -1 ;
                 notDone = false;
               }
             else
               { int item = 0 ;
                 if (ignore && isLeftComment(spec, new Position(line, 0)))
                   { item = 1 ; }
                 if (spec[line][item].column <= tok.column)
                   { notDone = false ;} ;
               }
           }; // END if (spec[line].length > 0)
         if (notDone) {line = line - 1 ;};
       } // END while ((line >= 0) && notDone)

     /**********************************************************************
     * If no covering line, return (-1, 0).                                *
     **********************************************************************/
     if (line == -1) {return new Position(-1, 0);} ;

     /**********************************************************************
     *      Find covering item.                                            *
     **********************************************************************/
     int item = 0;
     int nsItem = 0;
       /********************************************************************
       * item is the current item.                                         *
       * nsItem is the last non-subscript item found that covers tok.      *
       ********************************************************************/
     boolean dashFound = false ;
     if (spec[line][0].type == Token.DASHES)
      { dashFound = true;} ;
     while (    (! dashFound)
             && (item + 1 < spec[line].length)
             && (spec[line][item + 1].column <= tok.column))
          { if (spec[line][item+1].type == Token.DASHES)
             {dashFound = true;} ;
            item = item + 1;
            if (!spec[line][item].subscript)
                {nsItem = item;};
          };
     if (dashFound) {return new Position(-1, 0);} ;

     /**********************************************************************
     * Return (line, nsItem).                                              *
     **********************************************************************/
     return new Position(line, nsItem);
    } ;

  private static Position blockingPosition(Token[][] spec, Position p)
    /***********************************************************************
    * Searches upwards from position p to find the first token at the      *
    * same column or to the right of the token at p that is not            *
    * a subscript token.                                                   *
    ***********************************************************************/
    { int line = p.line - 1 ;
      int item = 0 ;
      Token tok = p.toToken(spec) ;
      boolean notDone = true ;
      while ((line >= 0) && notDone)
       { if (spec[line].length > 0)
           { if (spec[line][0].type == Token.PROLOG)
               { line = -1 ;
                 notDone = false;
               }
             else
               { item = 0 ;
                 if (isLeftComment(spec, new Position(line, 0)))
                   { item = 1 ; } ;
                 while (notDone && (item < spec[line].length))
                  { if (   (spec[line][item].column >= tok.column)
                        && (! spec[line][item].subscript))
                      { notDone = false ; }
                    else 
                      { item = item+1; };
                  } ;
               } ;
           }; // END if (spec[line].length > 0)
         if (notDone) {line = line - 1 ;} ;
       } // END while ((line >= 0) && notDone)

     /**********************************************************************
     * If no token found, return (-1, 0).                                  *
     **********************************************************************/
     if (line == -1) {return new Position(-1, 0);} ;

     /**********************************************************************
     * Return (line, item).                                                *
     **********************************************************************/
     return new Position(line, item);
    } ;

  private static void setSubscriptField(Token[][] spec)
    /***********************************************************************
    * Sets the subscript field of the tokens.  (This field is true iff     *
    * the token is part of a sub- or superscript.)  Upon encountering a    *
    * "^" or a token that is a built-in symbol with symbolType -           *
    * Symbol.SUBSCRIPTED token, the next token or all tokens in the        *
    * properly parenthesized expression that follows it are                *
    * subscripted--iff all those tokens lie on the same line.              *
    ***********************************************************************/
    { int line = 0 ;
      while (line < spec.length)
       { int item = 0 ;
         int startSub = -1 ;
           /****************************************************************
           * If a subscript has begun, then this is its first item;        *
           * otherwise, it equals -1.                                      *
           ****************************************************************/
         int nestingDepth = 0 ;
           /****************************************************************
           * The current parenthesis nesting level inside a subscript, or  *
           * 0 if not in a subscript.                                      *
           ****************************************************************/
           

         while (item < spec[line].length)
          { Token tok = spec[line][item] ;
              /*************************************************************
              * tok is the current token.                                  *
              *************************************************************/
            if (startSub == -1)
             { /************************************************************
               * A subscript has not yet begun.                            *
               ************************************************************/
               if (   (tok.type == Token.BUILTIN)
                   && (   (BuiltInSymbols.GetBuiltInSymbol(
                                                    tok.string, true).symbolType 
                            == Symbol.SUBSCRIPTED)
                       || (tok.string.equals("^"))))
                { 
                  startSub = item + 1 ;
                } // END then OF if ((tok.type == Token.BUILTIN) ...)
               else 
                { /*********************************************************
                  * Do nothing.                                            *
                  *********************************************************/
                }; // END else OF if ((tok.type = Token.BUILTIN) ...)

             }  // END then OF if (startSub == -1)
            else
             { /************************************************************
               * A subscript has begun.                                    *
               *                                                           *
               * Set symType to the symbol type of the token, or           *
               * NOT_A_SYMBOL if it isn't a symbol.                        *
               ************************************************************/
               int symType = Symbol.NOT_A_SYMBOL ;
               if (tok.type == Token.BUILTIN)
                 { symType = 
                      BuiltInSymbols.GetBuiltInSymbol(
                         tok.string, true).symbolType ;
                 };

               if (   (   (nestingDepth == 0) 
                       && (symType != Symbol.LEFT_PAREN))
                   || (   (nestingDepth == 1) 
                       && (symType == Symbol.RIGHT_PAREN)))
                { /*********************************************************
                  * This ends the subscript.  Set the subscript field of   *
                  * all tokens from startSub to item and reset startSub.   *
                  *********************************************************/
                  nestingDepth = 0 ;
                  while (startSub <= item)
                   { spec[line][startSub].subscript = true ;
                     startSub = startSub + 1;
                   }
                  startSub = -1 ;
                } // END then OF if (((nestingDepth == 0)... ))
               else
                { /*********************************************************
                  * The subscript continues.                               *
                  *********************************************************/
                  if (symType == Symbol.LEFT_PAREN)
                    { nestingDepth = nestingDepth + 1; }
                  else
                    { if (symType == Symbol.RIGHT_PAREN)
                        { nestingDepth = nestingDepth - 1; };
                    };
                }; // END else OF if (((nestingDepth == 0)... ))

             }; // END else OF if (startSub == -1)

           item = item + 1 ;
          } ; // END while (item < spec[line].length)


         line = line + 1;
       } // END while (line < spec.length)
      
    } ;
    
    
}

/* last modified on Sun  5 August 2012 at 17:07:48 PST by lamport */
