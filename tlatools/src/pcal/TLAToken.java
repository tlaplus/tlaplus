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
*                      BUILTIN, NUMBER, STRING, IDENT                      *
*                                                                          *
* The constructors are TLAToken() and TLAToken(string, column, type).      *
*                                                                          *
* The methods are                                                          *
*                                                                          *
*   getWidth() : returns width of token in input.                          *
*   toString() : for debugging                                             *
***************************************************************************/
package pcal;

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

      
    /***********************************************************************
    * Below are the methods for this object class, including the           *
    * constructor.                                                         *
    ***********************************************************************/
    public TLAToken(String str, int col, int typ)
      /*********************************************************************
      * A TLAToken constructor                                             *
      *********************************************************************/
      { string = str ;
        column = col ;
        type   = typ ;
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
          } ;
        String str = "\"" + string + "\"" ;
        if (string == null) {str = "null";};

        String result =    "[str |-> "    + str
                         + ", type |-> "  + typeName
                         + ", col |-> "   + column
                         + ", width |-> " + getWidth() 
                         + ", string |-> " + string ;
        return result; 
      };
 

   public TLAToken Clone()
     {return new TLAToken(this.string, this.column, this.type) ; 
     }

  }

/* last modified on Tue 26 Jul 2005 at  0:03:08 UT by lamport */
