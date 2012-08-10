// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS CommentToken                                                       *
* EXTENDS Token                                                            *
*                                                                          *
* A subclass of Token for a comment (a Token of type COMMENT).  In this    *
* subclass, the superclass's string field does not contain the "(*", "*)"  *
* or "\*" token.  Also, inner comments are stripped out.  This means       *
* that, if there are inner comments, the getWidth method returns the       *
* number of characters in the original comment that are not part of an     *
* inner comment.                                                           *
*                                                                          *
* The additional fields of the subclass are:                               *
*                                                                          *
*   rsubtype   : A "raw" subtype set by TokenizeSpec.Tokenize when         *
*                the token is created.                                     *
*                                                                          *
*   subtype    : A subtype for use in formatting the comment.  This        *
*                field is set by the ProcessComments method.               *
*                                                                          *
*   delimiters : Used to compute the width of the comment in the           *
*                original input.                                           *
***************************************************************************/
package tla2tex;

public class CommentToken extends Token
  { public int rsubtype ;
      /*********************************************************************
      * The "raw" subtype of the Token, set by the TokenizeSpec.Tokenize   *
      * method.  Below are its possible values, and their meanings.        *
      *********************************************************************/

      public static final int NORMAL = 1 ;
        /*******************************************************************
        * This is a "(* ... *)" comment on a single line.                  *
        *******************************************************************/

      public static final int LINE = 2 ;
        /*******************************************************************
        * This is a "\*" comment.                                          *
        *******************************************************************/

      public static final int BEGIN_OVERRUN = 3 ;
        /*******************************************************************
        * The first line of an overrun comment.                            *
        *******************************************************************/

      public static final int END_OVERRUN = 4 ;
        /*******************************************************************
        * The last line of an overrun comment.                             *
        *******************************************************************/
        
      public static final int OVERRUN = 5 ;
        /*******************************************************************
        * After tokenizing, this is a line in the middle of an overrun     *
        * comment.  With further processing, this subtype may be changed.  *
        *******************************************************************/

   public int subtype ;
      /*********************************************************************
      * The interpreted subtype, set by the ProcessComments method.        *
      * Below are its possible values, and their meanings.                 *
      *********************************************************************/
        public static final int ONE_LINE    = 6 ;
          /*****************************************************************
          * A comment that is typeset on a single line.                    *
          *****************************************************************/
          
        public static final int BEGIN_MULTI = 7 ;
          /*****************************************************************
          * The beginning of a multi-line end comment.                     *
          *****************************************************************/

        public static final int MULTI = 8 ;
          /*****************************************************************
          * A line of the body of a multi-line end comment.                *
          *****************************************************************/

        public static final int NULL = 9 ;
          /*****************************************************************
          * A line of "*"s that ends a multi-line comment, and is thus     *
          * not to be printed.                                             *
          *****************************************************************/
          
        public static final int PAR = 10 ;
          /*****************************************************************
          * A line of a paragraph comment--that is, one begun with a (*    *
          * that covers multiple lines before the *).  If the first or     *
          * last line of a paragraph comment is not the only token on the  *
          * line, then that line is turned into a one-line comment.        *
          *****************************************************************/
          
   private int delimiters = 0;
     /**********************************************************************
     * This is the number of comment delimiter characters deleted from     *
     * the string.  It is 4 for a "(* ... *)" comment, etc.                *
     **********************************************************************/
     
   public CommentToken(String str, int col, int sub, boolean pseudo)
     /**********************************************************************
     * The constructor for this class.  The third argument specifies the   *
     * rsubtype.  The fourth argument is true iff this comment is ended    *
     * by the beginning of a PlusCal algorithm or begun by the end of a    *
     * PlusCal algorithm.  In either case, two delimiter characters that   *
     * normally would have been deleted weren't.                           *
     **********************************************************************/
     { type    = Token.COMMENT; 
       column = col ;
       string  = str;
       rsubtype = sub;
       subtype = 0 ;
       switch (rsubtype)
         { case NORMAL :         delimiters = pseudo?2:4;
                                 break;
           case LINE :
           case BEGIN_OVERRUN :
           case END_OVERRUN :    delimiters = pseudo?0:2;
                                 break ;

           case OVERRUN :        break ;
           default : Debug.ReportBug(
                      "CommentToken constructor called with illegal subtype"
                      );
         } ;

     };     

   public int getWidth()
     /**********************************************************************
     * Returns the number of columns occupied by the token in the input.   *
     **********************************************************************/
     { if (string == null) {return 0;} ;
       return string.length() + delimiters ;
     }

   public static void ProcessComments(Token[][] spec)
      /*********************************************************************
      * This computes the subtype of each token, based on the rsubtypes.   *
      *                                                                    *
      * OVERRUN :                                                          *
      *    Set to PAR.                                                     *
      *                                                                    *
      * BEGIN_OVERRUN or END_OVERRUN :                                     *
      *    Set to PAR, and its column field set to 0, if it is the         *
      *    only token on the line.  Otherwise, it is changed to ONE_LINE.  *
      *                                                                    *
      * NORMAL or LINE :                                                   *
      *    If not part of a multiline comment, set to ONE_LINE.            *
      *                                                                    *
      *    If part of a multiline comment at least one of whose            *
      *    lines contains another token (which must be to the left),       *
      *    then set to BEGIN_MULTI, MULTI, or NULL depending               *
      *    on whether it is the first line, an inner line, or the          *
      *    (optional) end line.                                            *
      *                                                                    *
      *    If part of a multiline comment all of whose lines contain       *
      *    only this comment, then the first and (optional) end line       *
      *    are set to NULL and the inner lines are set to PAR.             *
      *                                                                    *
      *    Note: The first or end line of a multi-line comment is one      *
      *    that consists of all *'s or -'s for a NORMAL comment, and       *
      *    consists of at least 3 *'s or -'s followed by spaces and or     *
      *    *'s or -'s for a                                                *
      *    LINE comment.                                                   *
      *********************************************************************/
     { int line = 0 ;       
         /******************************************************************
         * The current line.                                               *
         ******************************************************************/

       int beginLine = -1 ; 
         /******************************************************************
         * The line beginning the current multi-line comment.              *
         ******************************************************************/

       while (line < spec.length)
        /*******************************************************************
        * Loop Invariant:                                                  *
        *   /\ 0 \leq item \leq = spec[line].length                        *
        *   /\ (beginLine # -1) <=>                                        *
        *        /\ beginLine is largest i < line s.t.                     *
        *               Last token of spec[beginLine] is a "******"        *
        *               comment.                                           *
        *        /\ \A i \in beginLine .. (line - 1) :                     *
        *             /\ Last token of spec[beginLine] is a comment.       *
        *             /\ spec[i].column =                                  *
        *                 spec[beginLine][spec[beginLine].length-1].column *
        *******************************************************************/
        { int item = 0;

          boolean beginMultiLine = false ;
               /************************************************************
               * Set to true if this should begin the next multi-line      *
               * comment.                                                  *
               ************************************************************/

          boolean endMultiLine = false ;
               /************************************************************
               * Set to true if this should end the previous multi-line    *
               * comment.                                                  *
               ************************************************************/
             
          while (item < spec[line].length)
           { 
             if (spec[line][item].type == COMMENT)
               { /**********************************************************
                 *                  This is a comment token.               *
                 **********************************************************/
                 boolean starLine = true ;
                   /********************************************************
                   * For the last token on the line, this is set false     *
                   * iff this is not a star comment.                       *
                   ********************************************************/
                 CommentToken tok = (CommentToken) spec[line][item] ;
                 if (item == spec[line].length - 1)
                   { /******************************************************
                     * This is the last token on the line.                 *
                     ******************************************************/

                     /******************************************************
                     * Set starLine to false if this is not a LINE or      *
                     * NORMAL "****" comment.                              *
                     ******************************************************/
                     if (   (   (tok.rsubtype != LINE)
                             && (tok.rsubtype != NORMAL))
                         || (tok.string.length() == 0))
                            /***********************************************
                            * A "\*" or "(**)" comment is not considered   *
                            * a star line.                                 *
                            ***********************************************/
                       { starLine = false; } ;
                     int ch = 0;
                     while (   starLine
                            && (ch < tok.string.length())
                            && (ch <= 3) )
                      { if (   (tok.string.charAt(ch) != '*')
                            && (tok.string.charAt(ch) != '-'))
                          { starLine = false; } ;
                        ch = ch+1 ;
                      } // end while
                     ch = 4;
                     while (   starLine
                            && (ch < tok.string.length()))
                      { if (   (tok.string.charAt(ch) != '*')
                            && (tok.string.charAt(ch) != '-')
                            && (tok.string.charAt(ch) != ' '))
                          { starLine = false; };
                        ch = ch+1 ;
                      } // end while

                     /******************************************************
                     * Set endMultiLine for a COMMENT token.               *
                     ******************************************************/
                     if (   (beginLine != -1)
                         && (   (   (tok.rsubtype != LINE)
                                 && (tok.rsubtype != NORMAL))
                             || (tok.column  != 
                                   spec[beginLine][
                                             spec[beginLine].length - 1].column)
                             || starLine ))
                        { endMultiLine = true ;}

                     /******************************************************
                     * Set beginMultiLine (only done for a COMMENT token). *
                     ******************************************************/
                     if (   starLine
                         && (   (beginLine == -1) 
                             || (tok.column  != 
                                   spec[beginLine][
                                      spec[beginLine].length - 1].column)))
                        /***************************************************
                        * Note: A non-aligned star line both ends and      *
                        * begins a multi-line comment.                     *
                        ***************************************************/
                        { beginMultiLine = true;} ;

                   }  // END then OF if (item == spec[line].length - 1)
                 else 
                   { /******************************************************
                     * This is not the last token on the line .            *
                     ******************************************************/
                     
                   }; // END else OF if (item == spec[line].length - 1)
                 /**********************************************************
                 * Set the subtype of the COMMENT token.                   *
                 **********************************************************/
                 switch (tok.rsubtype)
                   { case NORMAL :
                     case LINE   :
                       if (beginMultiLine)
                         { tok.subtype = BEGIN_MULTI ; }
                       else
                         { if (endMultiLine)
                            { 
                              if (starLine)
                                { tok.subtype = NULL ; }
                              else 
                                { tok.subtype = ONE_LINE ;} ; 
                            }
                          else
                            { if (   (beginLine != -1)
                                  && (item == spec[line].length - 1))
                                { tok.subtype = MULTI ;}
                              else
                                { tok.subtype = ONE_LINE ;} ; 
                            }
                         };
                       break ;

                     case BEGIN_OVERRUN :
                       if (item == 0)
                         { tok.subtype = PAR ;}
                       else
                         { tok.subtype = ONE_LINE ;} ;
                       break ;

                     case END_OVERRUN   :
                       if (item == spec[line].length - 1)
                         { tok.subtype = PAR ;}
                       else
                         { tok.subtype = ONE_LINE ;} ;
                       break ;

                     case OVERRUN :
                       tok.subtype = PAR ;
                       break ;

                     default :
                       Debug.ReportBug(
                        "Bad token rsubtype in CommentToken.ProcessComments");
                   } ; // END switch (tok.rsubtype)                 

                 /**********************************************************
                 * Set aboveAlign for NULL or MULTI comments.              *
                 **********************************************************/
                 if (   (tok.subtype == MULTI)
                     || (tok.subtype == NULL))
                   { tok.aboveAlign = 
                       new Position(beginLine, spec[beginLine].length - 1);
                   } ;


               } // END then OF if (spec[line][item].type == COMMENT)
             else
               { /**********************************************************
                 * This is not a comment token.                            *
                 *                                                         *
                 * Set endMultiLine true if a multi-line comment has       *
                 * been started and this is the last token on the line.    *
                 **********************************************************/
                 if (   (beginLine != -1)
                     && (item == spec[line].length - 1))
                   { endMultiLine = true ;}

               } ;  // END else OF if (spec[line][item].type == COMMENT)

             item = item + 1 ;
           }; // END while (item < spec[line].length)

          /**************************************************************
          * Set or reset beginLine if necessary.                        *
          **************************************************************/
          if (endMultiLine || (spec[line].length == 0))
            {beginLine = -1;} ;
          if (beginMultiLine) {beginLine = line;} ;

          line = line + 1 ;
        }; // END while (line < spec.length)
     }; // END ProcessComments(Token[][] spec)


   public String toString()
      /*********************************************************************
      * For debugging output.                                              *
      *********************************************************************/
      { String rstypeName = "";
        String stypeName = "";
        switch (rsubtype) 
          { case NORMAL        : rstypeName = "NORMAL"        ; break ;
            case LINE          : rstypeName = "LINE"          ; break ;
            case BEGIN_OVERRUN : rstypeName = "BEGIN_OVERRUN" ; break ;
            case END_OVERRUN   : rstypeName = "END_OVERRUN"   ; break ;
            case OVERRUN       : rstypeName = "OVERRUN"       ; break ;
          } ;
        switch (subtype) 
          { case ONE_LINE      : stypeName = "ONE_LINE"      ; break ;
            case BEGIN_MULTI   : stypeName = "BEGIN_MULTI"   ; break ;
            case MULTI         : stypeName = "MULTI"         ; break ;
            case NULL          : stypeName = "NULL"          ; break ;
            case PAR           : stypeName = "PAR"           ; break ;
          } ;
        return Misc.BreakLine( mostOfString() + 
                          ",\t subtype |-> " + stypeName + 
                          ",\t rsubtype |-> " + rstypeName + 
                          ",\t delim |-> " + delimiters + "]");
      };  

  }

/* last modified on Tue 18 Sep 2007 at  6:44:14 PST by lamport */
