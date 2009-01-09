// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS CToken                                                             *
*                                                                          *
* WARNING: THIS CLASS SEEMS TO HAVE BEEN OBTAINED BY MODIFYING THE TOKEN   *
* CLASS, AND THE COMMENTS WERE APPARENTLY NOT ALL MODIFIED APPROPRIATELY.  *
*                                                                          *
* A Token object represents a single token of the specification, where a   *
* token is either a single token of a TLA spec, a line of comment, or a    *
* line of the prolog or epilog.                                            *
*                                                                          *
* A Token object has the following fields:                                 *
*                                                                          *
*   String string : The actual input.                                      *
*   int column    : The column in the input line of its first              *
*                   character (counting from 0).                           *
*   int type      : The type of the token.  Possibilities are:             *
*                                                                          *
*   boolean isTLA : True if this token is to be interpreted as             *
*                   part of a TLA spec.                                    *
*                                                                          *
* The constructors are CToken() and CToken(string, column, type, isTLA).   *
*                                                                          *
* The methods are                                                          *
*                                                                          *
*   getWidth() : returns width of token in input.                          *
*   toString() : for debuggin                                              *
***************************************************************************/
package tla2tex;
import java.util.Vector;

public class CToken
  /*************************************************************************
  * This class defines the Token object, which is an element of a          *
  * tokenized specification.  It is expected that some token types may be  *
  * subclassed.  In particular, there will be a CommentToken class that    *
  * is a subclass of Token.  Every token of type COMMENT should belong to  *
  * this class.                                                            *
  *************************************************************************/
  { public String string;
      /*********************************************************************
      * The string of the token.  This is usually what the user has        *
      * typed, but it may also be something else.                          *
      *********************************************************************/

    public int column;
      /*********************************************************************
      * The column in which the first character of the token appears in    *
      * the input.                                                         *
      *********************************************************************/
      
    public boolean isTLA;
      /*********************************************************************
      * True if this token is to be interpreted as part of a TLA spec.     *
      *********************************************************************/

    public boolean isAmbiguous;
      /*********************************************************************
      * True if this token could be either a spec token or part of         *
      * ordinary text.                                                     *
      *********************************************************************/
      
    public int type ;
       /********************************************************************
       * The type of the token.  Here are the possibilities:               *
       ********************************************************************/
       public static final int BUILTIN = 1 ;
         /******************************************************************
         * A built-in token.                                               *
         ******************************************************************/

       public static final int NUMBER = 2 ;
         /******************************************************************
         * A number like "2" or "\O777".                                   *
         ******************************************************************/

       public static final int STRING = 3 ;
         /******************************************************************
         * A string like "foo".  In this type, the string field does not   *
         * contain the enclosing quotes.                                   *
         ******************************************************************/

       public static final int IDENT = 4 ;
         /******************************************************************
         * An identifier, such as foo_Bar.                                 *
         ******************************************************************/

       public static final int OTHER = 5 ;
         /******************************************************************
         * A comment.  This will be subclassed to include an additional    *
         * field containing the tokenization of the comment.               *
         ******************************************************************/
         
       public static final int REP_CHAR = 6 ;
         /******************************************************************
         * A sequence of repeated repeatChar characters.                   *
         ******************************************************************/

       public static final int LEFT_DQUOTE = 7 ;
         /******************************************************************
         * A left double-quote token.                                      *
         ******************************************************************/

       public static final int RIGHT_DQUOTE = 8 ;
         /******************************************************************
         * A right double-quote token.                                     *
         ******************************************************************/

       public static final int VERB = 9 ;
         /******************************************************************
         * A string that is to be typeset verbatim.                        *
         ******************************************************************/

       public static final int TEX = 10 ;
         /******************************************************************
         * A string that is to be typeset as TeX input.                    *
         ******************************************************************/

       public static final int NULL = 11 ;
         /******************************************************************
         * A special null token.                                           *
         ******************************************************************/

       public static final int PF_STEP = 12;
         /******************************************************************
         * This is a proof-step number, such as "<42>" or "<37>2a.".       *
         * It shouldn't make any difference, but the definitions of        *
         * PF_STEP in Token and CToken are made the same just in case.     *
         ******************************************************************/
      
    /***********************************************************************
    * Below are the methods for this object class, including the           *
    * constructor.                                                         *
    ***********************************************************************/
    public CToken(String str, int col, int typ, boolean tla, boolean amb)
      /*********************************************************************
      * A CToken constructor.                                              *
      *********************************************************************/
      { string = str ;
        column = col ;
        type   = typ ;
        isTLA  = tla ;
        isAmbiguous = amb ;
      }

    public CToken()
      /*********************************************************************
      * A default Token constructor, apparently needed for subclasses.     *
      *********************************************************************/
      { string = "" ;
        column = 0 ;
        type   = 0 ;
        isTLA  = false ;
      } ;

    public static CToken nullCToken = new CToken("", 0, NULL, false, false) ;
      /*********************************************************************
      * A special null CToken.                                             *
      *********************************************************************/
      
    public int getWidth() 
      /*********************************************************************
      * Returns a width, which is the number of columns the token spans    *
      * in the original input stream.                                      *
      *********************************************************************/
      { if (string == null) 
          {return 0;}
        else
          { if (type == STRING)
              { return string.length() + 2; }
          }
       return string.length();
      };      

    /***********************************************************************
    * The method FindPfStepCTokens replaces each sequence of three to five *
    * tokens created by a TokenizeComment method for something like        *
    * "<42>" or "<42>1a." into a single token of type PF_STEP.             *
    ***********************************************************************/
    static void FindPfStepCTokens(CToken[][] toks) {
      boolean lastIsTLA = false ;
      for (int k = 0 ; k < toks.length ; k++) 
        { CToken[] input = toks[k] ;
          Vector outputVec = new Vector(input.length) ;
          int i = 0 ;
          while (i < input.length)
           { if (   (i < input.length - 2)
                 && (input[i].string.equals("<"))
                 && (input[i+1].column == input[i].column + 1)
                 && (input[i+1].type == NUMBER)
                 && (input[i+2].string.equals(">"))
                 && (input[i+2].column == 
                         input[i+1].column + input[i+1].getWidth()) )
               { int numOfToks = 3 ;
                 String str = "<" + input[i+1].string + ">" ;
                 if (   (i < input.length - 3)
                     && (input[i+3].column == input[i+2].column + 1)
                     && (   (input[i+3].type == NUMBER)
                         || (input[i+3].type == IDENT)))
                   { str = str + input[i+3].string ;
                     numOfToks = 4;
                     if (   (i < input.length - 4)
                         && (input[i+4].column == 
                               input[i+3].column + input[i+3].getWidth())
                         && (input[i+4].string.equals(".")))
                       { str = str + "." ;
                         numOfToks = 5;
                       } ;
                   };
                 outputVec.addElement(new CToken(str,
                                                input[i].column,
                                                PF_STEP,
                                                input[i].isTLA,
                                                input[i].isAmbiguous) );
                 i = i + numOfToks;
               } // if
             else { outputVec.addElement(input[i]) ;
                    i = i+1 ;
                  } // else
           } ; // while
          if (outputVec.size() != input.length)
            { toks[k] = new CToken[outputVec.size()] ;
              for (i = 0; i < outputVec.size(); i++) 
                 { toks[k][i] = (CToken) outputVec.elementAt(i) ;
                 } ;
            }
        } // for k
      } 

    /***********************************************************************
    * The following defines a toString() method for printing a Token for   *
    * debugging.  To do a decent job, it splits it into reasonably-sized   *
    * lines, using the Misc.BreakLine method.                              *
    ***********************************************************************/
    public String mostOfString()
      /*********************************************************************
      * This returns everything in toString() except the final "]", so it  *
      * can be used by the toString() method of subclasses.                *
      *********************************************************************/
      { String typeName = "";
        switch (type) 
          { case BUILTIN      : typeName = "BUILTIN"       ; break ;
            case NUMBER       : typeName = "NUMBER"        ; break ;
            case STRING       : typeName = "STRING"        ; break ;
            case IDENT        : typeName = "IDENT"         ; break ;
            case OTHER        : typeName = "OTHER"         ; break ;
            case REP_CHAR     : typeName = "REP_CHAR"      ; break ;
            case LEFT_DQUOTE  : typeName = "LEFT_DQUOTE"   ; break ;
            case RIGHT_DQUOTE : typeName = "RIGHT_DQUOTE"  ; break ;
            case VERB         : typeName = "VERB"          ; break ;
            case TEX          : typeName = "TEX"           ; break ;
          } ;
        String str = "\"" + string + "\"";
        if (string == null) {str = "null";};

        String result =    "[str |-> "    + str
                         + ",\t type |-> "  + typeName
                         + ",\t col |-> "   + column
                         + ",\t width |-> " + getWidth() ;
        if (isTLA) 
          {result = result + ",\t isTLA |-> true";};
        if (isAmbiguous)
          {result = result + ",\t isAmbig |-> true";};
        return result; 
      };
      

    public String toString()
      /*********************************************************************
      * For debugging.                                                     *
      *********************************************************************/
      {  return Misc.BreakLine(mostOfString() + "]") ; };  

  }
