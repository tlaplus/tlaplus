/***************************************************************************
* CLASS TLAToken                                                           *
*                                                                          *
* A TLAToken object represents a single token of a TLA+ expression.        *
*                                                                          *
* A TLAToken object has the following fields:                              *
*                                                                          *
*   String string : The actual input.                                      *
*   int column    : The column in the input line of its first              *
*                   character (counting from 0).                           *
*   int type      : The type of the token.  Possibilities are:             *
*                      BUILTIN, NUMBER, STRING, IDENT, ADDED               *
*                                                                          *
* The constructors are TLAToken() and TLAToken(string, column, type).      *
*                                                                          *
* The methods are                                                          *
*                                                                          *
*   getWidth() : returns width of token in input.                          *
*   toString() : for debugging                                             *
***************************************************************************/
package pcal;

import java.util.Vector;

public class TLAToken
  /*************************************************************************
  * This class defines the TLAToken object, which is an element of a       *
  * tokenized expression.                                                  *
  *************************************************************************/
  { public String string ;
      /*********************************************************************
      * The string of the token.  This is usually what the user has        *
      * typed, but it may also be something else.                          *
      *********************************************************************/

    public int column ;
      /*********************************************************************
      * The column in which the first character of the token appears in    *
      * the expression.                                                    *
      *********************************************************************/
      
    public int type ;
       /********************************************************************
       * The type of the token.  Here are the possibilities:               *
       ********************************************************************/
    
    public Region source ;
       /********************************************************************
       * The region in the file occupied by the token in the PlusCal       *
       * code.  Added 6 Dec 2011 for TLA to PlusCal mapping.               *
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

       public static final int ADDED = 5 ;
         /******************************************************************
         * A token "pc" or "stack" has this type when it has been added    *
         * by the translator, and so it should be given a subscript if     *
         * this is a multiprocess algorithm.  It doesn't matter whether    *
         * or not the translator uses this type for other tokens it        *
         * creates.                                                        *
         ******************************************************************/
       
       /**
        * A BEGIN/END_REPLACEMENT token is a zero-width token, with
        * string "", that marks the beginning/end of a region of an
        * expression obtained by substituting an expression for a token.
        * The beginning and end  of the region of the BEGIN_REPLACEMENT 
        * token both equal the begin location of the replaced token; the 
        * beginning and end of the region of the END_REPLACEMENT token
        * both equal the end region of the replaced token.
        */
//       public static final int BEGIN_REPLACEMENT = 6 ;
//       public static final int END_REPLACEMENT = 7 ;
      
    /**
     * The beginSubst and endSubst fields represent sequences of Paren objects in a TPMap, 
     * as described in module TLAtoPCal.  This means that they indicate the beginning
     * and ending of substitutions that created the expression containing the token.
     * Here is an example.  
     * 
     *    macro foo(a) {
     *     x := a + 1 
     *    }
     *    macro bar(b) {
     *      foo(b)
     *    }
     *    ...
     *    bar(3+2) ;
     *    
     * After macro expansion, the call of foo in macro bar is replaced by
     * 
     *     x := b + 1
     * 
     * and the call of bar is replaced by
     * 
     *    x := (3+2)+1
     * 
     * The token "b" in "x := b" will have 
     * 
     *    beginSubst = <<beginLoc(a)>> and endSubst = <<endLoc(a)>> 
     *    
     * where beginLoc(a) and endLoc(a) are the beginning and end locations of the 
     * token "a" in expression "x := a + 1" of macro foo.  The token "(" in 
     * "x := (3+2)+1" will have
     * 
     *    beginSubst = << beginLoc(a), beginLoc(b) >> and  endSubst = << >>
     *    
     * and the ")" token would have 
     * 
     *    beginSubst =  << >> and endSubst = << endLoc(a), endLoc(b) >>
     * 
     * (It was an arbitrary choice to add the begin/endLoc(b) elements to the 
     * beginning of the begin/endSubst sequences rather than to the end.)
     * 
     * Note that there's no need for the TPMap to have the extra Parens corresponding
     * to the location of "b".  It wouldn't be needed if  substituting an expression containing
     * more than one token for a token always adds parentheses around the substituted
     * expression.  This would imply that if some token has beginSubst equal to a sequence
     * of beginLoc locations, then some token (perhaps the same one) has a its
     * endSubst equal to the corresponding sequence of endLoc locations.  As in the,
     * example, there would be no need to keep anything but the first element of the
     * sequence, which is what is done.  However, since the {@link TLAExpr#substituteAt} 
     * method is sometimes called with an argument telling it not to  add
     * parentheses when substituting multiple tokens, I'm letting beginSubst and endSubst
     * be sequences (Vectors) of PCalLocation objects.  It would be a good idea to
     * remove redundant pairs of matching parens (the ones for "b" in the example), and
     * perhaps I'll do that.
     */
    private Vector beginSubst = new Vector(2) ; // of PCalLocation
    private Vector endSubst = new Vector(2);    // of PCalLocation
    public Vector getBeginSubst() {
        return beginSubst;
    }

    public void setBeginSubst(Vector beginSubst) {
        this.beginSubst = beginSubst;
    }

    public Vector getEndSubst() {
        return endSubst;
    }

    public void setEndSubst(Vector endSubst) {
        this.endSubst = endSubst;
    }
    

    /**
     * The isAppended flag is true iff this token is a prime ("'")
     * or one of the tokens in the "[self]" that is effectively added
     * to an expression immediately after an IDENT token by the 
     * {@link PcalTLAGen#AddSubscriptsToExpr} method.
     */
    private boolean isAppended = false ;
    public boolean isAppended() {
        return isAppended;
    }

//    public void setAppended(boolean isAppended) {
//        this.isAppended = isAppended;
//    }


    /***********************************************************************
    * Below are the methods for this object class, including the           *
    * constructors.                                                        *
    ***********************************************************************/
    /**
     * This is the old constructor, used before the addition of the TLA-PCal
     * mapping.  It should be used only to construct tokens that do not come
     * from a corresponding token in the PCal code. 
     * 
     * @param str
     * @param col
     * @param typ
     */
    public TLAToken(String str, int col, int typ)
      /*********************************************************************
      * A TLAToken constructor                                             *
      *********************************************************************/
      { string = str ;
        column = col ;
        type   = typ ;
        source = null ;
      }
    
    /**
     * The following constructor added for TLA-PCal mapping.  It 
     * sets the source field.
     * 
     * @param str
     * @param col
     * @param typ
     * @param line
     */
    public TLAToken(String str, int col, int typ, int line)
    /*********************************************************************
    * A TLAToken constructor                                             *
    *********************************************************************/
    { string = str ;
      column = col ;
      type   = typ ;
      source = new Region(line, col, str.length()) ;
    }
    
    /**
     * A constructor for cases in which the source region is known.
     * 
     * @param str
     * @param col
     * @param typ
     * @param src
     */
    public TLAToken(String str, int col, int typ, Region src) {
    	string = str ;
        column = col ;
        type   = typ ;
        source = src ;
    }
    
    /**
     * A constructor used only in {@link PcalTLAGen#AddSubscriptsToExpr}
     * or in Gen... methods that use it to construct tokens for the
     * TLAExpr argument of a call AddSubscriptsToExpr  
     * to create a token with isAppended = true.
     * 
     * @param str
     * @param col
     * @param typ
     * @param appended
     */
    public TLAToken(String str, int col, int typ, boolean appended) {
        string = str ;
        column = col ;
        type   = typ ;
        source = null ;
        isAppended = true ;
    }
    
    public TLAToken()
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
           * Have to compensate for the removal of the quotes.             *
           ****************************************************************/
            return string.length() + 2;}
        else
          {return string.length();}
      };      

   public String toString()
      /*********************************************************************
      * This is used to print a TLAToken for debugging.                    *
      *********************************************************************/
      { String typeName = "";
        switch (type) 
          { case BUILTIN    : typeName = "BUILTIN"    ; break ;
            case NUMBER     : typeName = "NUMBER"     ; break ;
            case STRING     : typeName = "STRING"     ; break ;
            case IDENT      : typeName = "IDENT"      ; break ;
//            case BEGIN_REPLACEMENT : typeName = "(map"  ; break ;
//            case END_REPLACEMENT   : typeName = "map)"  ; break ;    
          } ;
        String str = "\"" + string + "\"" ;
        if (string == null) {str = "null";};

        String result =    "[str |-> "    + str
                         + ", type |-> "  + typeName
                         + ", col |-> "   + column
                         + ", source |->" + 
            ((source == null) ? "null" : source.toString())
                         + ", beginSub |-> " + beginSubst.toString()
                         + ", endSub |-> " + endSubst.toString() + "]";
//                         + ", width |-> " + getWidth() 
//                         + ", string |-> " + string ;
        
//        if (source != null) {
//        	result = result + ", " + source.toString();
//        }
        return result; 
      };
 

   /**
    * Modified by LL on 6 Dec 2011 to set the source field too.
    * And on 14 Dec 2011 to set the beginSubst and endSubst fields.
    * 
    * @return
    */
   public TLAToken Clone()
     { 
	   TLAToken result = new TLAToken(this.string, this.column, this.type) ;
	   result.source = this.source ;
	   result.beginSubst = (Vector) this.beginSubst.clone();
	   result.endSubst = (Vector) this.endSubst.clone();
	   result.isAppended = this.isAppended;
	   return result ;
     }

  }

/* last modified on Tue 26 Jul 2005 at  0:03:08 UT by lamport */
