// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS Token                                                              *
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
*                      BUILTIN, NUMBER, STRING, IDENT, COMMENT,            *
*                      DASHES, END_MODULE, PROLOG, EPILOG,                 *
*                      PF_STEP                                             *
*   Position aboveAlign                                                    *
*   Position belowAlign                                                    *
*   float preSpace                                                         *
*   boolean isAlignmentPoint                                               *
*   float distFromMargin     : See the FindAlignments class.               *
*                                                                          *
* The constructors are Token() and Token(string, column, type).            *
*                                                                          *
* The methods are                                                          *
*                                                                          *
*   getWidth() : returns width of token in input.                          *
*   toString() : for debugging                                             *
*                                                                          *
* Every token of type COMMENT should belong to the subclass CommentToken.  *
***************************************************************************/
package tla2tex;
import java.util.Vector;

public class Token
  /*************************************************************************
  * This class defines the Token object, which is an element of a          *
  * tokenized specification.  It is expected that some token types may be  *
  * subclassed.  In particular, there will be a CommentToken class that    *
  * is a subclass of Token.  Every token of type COMMENT should belong to  *
  * this class.                                                            *
  *************************************************************************/
  { public String string ;
      /*********************************************************************
      * The string of the token.  This is usually what the user has        *
      * typed, but it may also be something else.                          *
      *********************************************************************/

    public int column ;
      /*********************************************************************
      * The column in which the first character of the token appears in    *
      * the input.                                                         *
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

       public static final int COMMENT = 5 ;
         /******************************************************************
         * A comment.  This will be subclassed to include an additional    *
         * field containing the tokenization of the comment.               *
         ******************************************************************/
         
       public static final int DASHES = 6 ;
         /******************************************************************
         * At least four "-"s.  May be either a separator or part of       *
         * "----- MODULE foo ------"                                       *
         ******************************************************************/

       public static final int END_MODULE = 7 ;
         /******************************************************************
         * A "========" string that ends a module.                         *
         ******************************************************************/

       public static final int PROLOG = 8 ;
         /******************************************************************
         * This is a string (usually a complete line) that appeared        *
         * before the beginning of the module.                             *
         ******************************************************************/

       public static final int EPILOG = 9 ;
         /******************************************************************
         * This is a line that appeared after the end of the module.       *
         ******************************************************************/

       public static final int PF_STEP = 12;
         /******************************************************************
         * This is a proof-step number, such as "<42>" or "<37>2a.".       *
         * It shouldn't make any difference, but the definitions of        *
         * PF_STEP in Token and CToken are made the same just in case.     *
         ******************************************************************/

       public static final int PCAL_LABEL = 13;
         /******************************************************************
         * This is a  label.  The string contains the label, the following *
         * ":" and perhaps a following "+" or "-".                         *
         ******************************************************************/

    /***********************************************************************
    * The following fields are specific to TLATeX. They are set to         *
    * non-default values only after the object has been created.           *
    ***********************************************************************/
    public Position aboveAlign  = new Position() ;
      /*********************************************************************
      * The position of the token in the tokenized spec with which         *
      * this token is to be left-aligned.  The specified item is always    *
      * in a line above the current token.  For a MULT or NULL comment     *
      * subtype, it points to the token that begins the multi-line         *
      * comment If aboveAlign.line = -1, then the token is to be           *
      * left-aligned with respect to the left margin.                      *
      *********************************************************************/
    public float preSpace =  0 ;
      /*********************************************************************
      * The amount of space to be added just before this token in the      *
      * final output.                                                      *
      *********************************************************************/
      
    public boolean subscript = false ;
      /*********************************************************************
      * Set true by FindAlignments.FindAlignments if this is token is part *
      * of a subscript or superscript.                                     *
      *********************************************************************/
      
    public Position belowAlign = new Position() ;
      /*********************************************************************
      * If belowAlign.line != -1, then belowAlign is the position of a     *
      * token on a lower line with which this token is to be aligned.      *
      * See the FindAlignments class for an explanation of the meaning of  *
      * this field.                                                        *
      *********************************************************************/

    /***********************************************************************
    * The aboveAlign and belowAlign fields of a spec maintain the          *
    * following invariant, which asserts that, for all tokens in a path    *
    * traced by belowAlign pointers, the aboveAlign field points to the    *
    * first token in the path.                                             *
    *                                                                      *
    *   \A pos : LET t == pos.toToken(spec)                                *
    *            IN  (t.belowAlign.line # -1) =>                           *
    *                  (t.belowAlign.toToken(spec).aboveAlign =            *
    *                     IF t.aboveAlign.line # -1 THEN t.aboveAlign      *
    *                                               ELSE pos               *
    ***********************************************************************/
    
    public boolean isAlignmentPoint = false ;
      /*********************************************************************
      * True iff some token is being aligned on this token, so we need to  *
      * find the distance from the left margin of this token.  The value   *
      * is true iff this token is the target of an aboveAlign or           *
      * belowAlign "pointer", or it is a multi-line comment that is not    *
      * the first token on its line.                                       *
      *********************************************************************/

    public float distFromMargin  =  0 ;
      /*********************************************************************
      * If isAlignmentPoint = true, then this is the distance in points    *
      * from the left-margin of the left-hand character in the token, as   *
      * reported by the alignment file's log output file.  The distance    *
      * from the margin in the final output of a token will be its         *
      * distFromMargin plus the sum of the preSpace for it and all         *
      * non-left-comment tokens to its left.                               *
      *********************************************************************/
      
    /***********************************************************************
    * Below are the methods for this object class, including the           *
    * constructor.                                                         *
    ***********************************************************************/
    public Token(String str, int col, int typ)
      /*********************************************************************
      * A Token constructor                                                *
      *********************************************************************/
      { string = str ;
        column = col ;
        type   = typ ;
      }

    public Token()
      /*********************************************************************
      * A default Token constructor, apparently needed for subclasses.     *
      *********************************************************************/
      { string = "" ;
        column = 0 ;
        type   = 0 ;
      } ;

    public int getWidth() 
      /*********************************************************************
      * Returns a width, which is the number of columns the token spans    *
      * in the original input stream.                                      *
      *********************************************************************/
      { if (string == null) 
          {return 0;}
        else if (type == STRING)
          {/****************************************************************
           * Have to compensate for the removal of the quotes.            **
           ****************************************************************/
            return string.length() + 2;}
        else
          {return string.length();}
      };      

    /***********************************************************************
    * The method FindPfStepTokens replaces each sequence of three to five  *
    * tokens created by TokenizeSpec for something like "<42>" or          *
    * "<42>1a." into a single token of type PF_STEP.                       *
    ***********************************************************************/
    static void FindPfStepTokens(Token[][] toks) {
      for (int k = 0 ; k < toks.length ; k++) 
        { Token[] input = toks[k] ;
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
                 boolean needsSpace = true ;
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

                 if (   (i < input.length - numOfToks)
                     && (input[i + numOfToks].type == BUILTIN)
                     && (   (BuiltInSymbols.GetBuiltInSymbol(
                                 input[i + numOfToks].string, true).symbolType
                              == Symbol.INFIX)
                         ||  (BuiltInSymbols.GetBuiltInSymbol(
                                 input[i + numOfToks].string, true).symbolType
                              == Symbol.PUNCTUATION)))
                   { needsSpace = false ; } ;
                 outputVec.addElement(new Token.PfStepToken
                                        (str,
                                         input[i].column,
                                         needsSpace) );
                 i = i + numOfToks;
               } // if
             else { outputVec.addElement(input[i]) ;
                    i = i+1 ;
                  } // else
           } ; // while
          if (outputVec.size() != input.length)
            { toks[k] = new Token[outputVec.size()] ;
              for (i = 0; i < outputVec.size(); i++) 
                 { toks[k][i] = (Token) outputVec.elementAt(i) ;
                 } ;
            }
        } // for k
      } 
    
    /***********************************************************************
    * The following defines a toString() method for printing a Token for   *
    * debugging.  To do a decent job, it splits it into reasonably-sized   *
    * lines, using the BreakLine method.                                   *
    ***********************************************************************/

    public String mostOfString()
      /*********************************************************************
      * This returns everything in toString() except the final "]", so it  *
      * can be used by the toString() method of subclasses.                *
      *********************************************************************/
      { String typeName = "";
        switch (type) 
          { case BUILTIN    : typeName = "BUILTIN"    ; break ;
            case NUMBER     : typeName = "NUMBER"     ; break ;
            case STRING     : typeName = "STRING"     ; break ;
            case PF_STEP    : typeName = "PF_STEP"    ; break ;
            case IDENT      : typeName = "IDENT"      ; break ;
            case COMMENT    : typeName = "COMMENT"    ; break ;
            case DASHES     : typeName = "DASHES"     ; break ;
            case END_MODULE : typeName = "END_MODULE" ; break ;
            case PROLOG     : typeName = "PROLOG"     ; break ;
            case EPILOG     : typeName = "EPILOG"     ; break ;
            case PCAL_LABEL : typeName = "PCAL_LABEL" ; break ;
          } ;
        String str = "\"" + string + "\"" ;
        if (string == null) {str = "null";};

        String result =    "[str |-> "    + str
                         + ",\t type |-> "  + typeName
                         + ",\t col |-> "   + column
                         + ",\t width |-> " + getWidth() ;
        if (aboveAlign.line != -1)
             {result = result + ",\t above |-> " + aboveAlign.toString();} ;
        if (belowAlign.line  != -1)
             {result = result + ",\t below |-> " + belowAlign.toString();} ;
        if (preSpace != 0)
             {result = result + ", space |-> " + preSpace; } ;
        if (isAlignmentPoint)
             {result = result + ", align |-> true"; } ;
        if (distFromMargin != 0)
             {result = result + ", dist |-> " + distFromMargin; } ;
        if (subscript) 
             {result = result + ", sub |-> true";};
        return result; 
      };
      

    public String toString()
      /*********************************************************************
      * For debugging.                                                     *
      *********************************************************************/
      {  return Misc.BreakLine(mostOfString() + "]") ; };  


    /***********************************************************************
    * We define a subclass to add a needsSpace field to PF_STEP tokens.    *
    ***********************************************************************/
    public static class PfStepToken extends Token { 
      public boolean needsSpace ;
        /*******************************************************************
        * This will be false iff the token is immediately followed by an   *
        * infix operator.                                                  *
        *******************************************************************/
        
      /*********************************************************************
      * The constructor.                                                   *
      *********************************************************************/
      public PfStepToken(String str, int col, boolean space) {
        super(str, col, PF_STEP) ;
        needsSpace = space ;
       }
     }

  }

/* last modified on Wed 19 Sep 2007 at  6:25:02 PST by lamport */
