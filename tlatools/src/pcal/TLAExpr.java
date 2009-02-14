/***************************************************************************
* CLASS TLAExpr                                                            *
*                                                                          *
* A TLAExpr is a representation of any part of a TLA+ specification.  It   *
* usually represents an expression, but can be used to represent           *
* sequences of declarations and definitions--including the complete        *
* translation.                                                             *
*                                                                          *
* A TLAExpr expr contains the following fields and methods:                *
*                                                                          *
*    tokens       : A vector of lines, where a line is a vector of tokens. *
*                   We say that expr is NORMALIZED iff expr.tokens has     *
*                   no non-empty line, or it has a non-empty line whose    *
*                   first token is in column 0.                            *
*                                                                          *
*    anchorTokens : An array of TLAToken's of the same length as           *
*                   expr.tokens, where expr.anchorTokens[i] is the anchor  *
*                   of line i.  (The definition of an anchor token is in   *
*                   Section 9.1 of the +Cal language document.)            *
*                                                                          *
*    anchorTokCol : An array of int's, of the same length as expr.tokens,  *
*                   where if expr.anchorTokens[i] is non-null, then        *
*                   expr.anchorTokCol[i] was the value of                  *
*                   (expr.anchorTokens[i]).column when the normalize       *
*                   method was called.                                     *
*                                                                          *
* If expr comes from an expression taken directly from the algorithm,      *
* then it evolves as follows.  First, expr is built up token by token,     *
* using the methods expr.addToken and expr.addLine methods.  It is then    *
* normalized and expr.anchorTokCol and expr.anchorTokens are computed by   *
* calling expr.normalize().  Additional tokens may then be added.  Adding  *
* a token modifies the columns of the tokens to the right, but it does     *
* not modify expr.anchorTokens or expr.anchorTokCol.  The renormalize      *
* method should be called after adding a sequence of tokens (such as by    *
* substituting an expression for a token) to adjust the anchorTokens and   *
* anchorTokCol fields before any more tokens are added to the expression.  *
*                                                                          *
* Here are the methods.                                                    *
*                                                                          *
*    addToken(tok) : Adds the TLAToken tok to the end of the last line.    *
*                    Note that tok.column must have the proper value       *
*                    for the expression produced by the method to be       *
*                    sensible.                                             *
*                                                                          *
*    addTokenOffset(tok, offset) :                                         *
*                    Adds the TLAToken tok to the end of the last line,    *
*                    setting tok's column so the token appears offset      *
*                    characters to the right of the last token on the      *
*                    line.  (Added 30 Aug 2007.)                           *
*                                                                          *
*    addLine()     : Adds an empty line to the end.  (Must be called       *
*                    before the first call of addToken.)                   *
*                                                                          *
*    normalize()   : Removes empty lines at the end of the expression      *
*                    and computes anchorTokens and anchorTokCol as         *
*                    explained above.                                      *
*                                                                          *
*    renormalize() : Recomputes anchorTokens and anchorTokCol as           *
*                    explained above.                                      *
*                                                                          *
*    toStringVector() :                                                    *
*      Equals a Vector of strings, each being the ASCII representation     *
*      of the corresponding line of expr.  If expr.anchorTokens[i] is      *
*      non-null, then an extra                                             *
*                                                                          *
*         (expr.anchorTokens[i]).column - expr.anchorTokCol[i]             *
*                                                                          *
*      spaces are added to the beginning of line i to maintain the         *
*      original indentation.                                               *
*                                                                          *
*    toString() :                                                          *
*       This converts an expr into a string that is its TLA+               *
*       representation in the AST module.  It is used for                  *
*       the -spec option, and for debugging.                               *
*                                                                          *
*    cloneAndNormalize() :                                                 *
*       Used to create a clone of the current expression.                  *
*                                                                          *
*    prepend(expr, spaces) :                                               *
*       Prepends the expression expr to the current expression,            *
*       leaving `spaces' spaces between the end of expr and the            *
*       first token of the original expression.                            *
*                                                                          *
*    substituteForAll(exprs, strs, parenthesize) :                         *
*       Substitutes the expressions in the vector exprs of TLAExpr         *
*       objects for the identifiers in the vector strs of strings.         *
*       If parenthesize = true, then put parentheses around the            *
*       substituted expression unless it or the current expression         *
*       consists of just one token.                                        *
*                                                                          *
*    substituteForAll(exprs, strs) :                                       *
*       Same as substituteForAll(exprs, strs, true).  (Kept for            *
*       compatibility after the third argument was added.)                 *
*                                                                          *
*    SeqSubstituteForAll(expVec, exprs, strs) :                            *
*       A vector of expressions obtained from the vector expVec of         *
*       expressions by cloning each of them and then                       *
*       substituting the expressions in the vector exprs of TLAExpr        *
*       objects for the identifiers in the vector strs of strings.         *
*                                                                          *
* There are quite a few other methods used to implement these that might   *
* be of use for manipulating expressions.  Search below for "SUBSTITUTING  *
* IN EXPRESSIONS" to find them.                                            *
***************************************************************************/
package pcal;
import java.util.Vector;

import pcal.exception.TLAExprException;
import pcal.exception.UnrecoverableException;

public class TLAExpr
  { public Vector tokens       = new Vector();
    public TLAToken[] anchorTokens = null;
    public int[]      anchorTokCol = null;

    TLAExpr()
      /*********************************************************************
      * A constructor for an empty object of class TLAExpr.                *
      *********************************************************************/
    { }
      
    TLAExpr(Vector t)
      /*********************************************************************
      * A constructur that builds a new, unnormalized TLAExpr with a       *
      * given tokens Vector.                                               *
      *********************************************************************/
     {tokens = t ;
      anchorTokens = null;
      anchorTokCol = null;
     }

    public void addToken(TLAToken tok)
      {  ((Vector) tokens.elementAt(tokens.size()-1)).addElement(tok) ;
      } ;


    /***********************************************************************
    * The addTokenOffset method was added by LL on 30 Aug 2007 to fix the  *
    * following bug.  When a prime or "[self]" is appended to a variable   *
    * v, the sustituteForAll() method is called to replace the token "v"   *
    * with an expression consisting of a line having the sequence of       *
    * tokens                                                               *
    *                                                                      *
    *    "v"  "'"   or   "v" "[" "self" "]"                                *
    *                                                                      *
    * However, every token in this expression had column 0, which caused   *
    * the renormalize() method to mess up alignment and even halt with     *
    * the error                                                            *
    *                                                                      *
    *   "TLAExpr.renormalize() found anchor has moved to left."            *
    *                                                                      *
    * To fix this, the calls in PcalTLAGen.java to addToken() that were    *
    * used to create the new expression were replaced by calls to          *
    * addTokenOffset.                                                      *
    ***********************************************************************/
    public void addTokenOffset(TLAToken tok, int offset)
      {  Vector lastLine = (Vector) tokens.elementAt(tokens.size()-1) ;
         int newCol = offset ;
         if (lastLine.size() > 0) 
           { TLAToken lastTok = 
                (TLAToken) lastLine.elementAt(lastLine.size()-1) ;
            newCol = newCol + lastTok.column + lastTok.string.length() ;
           } ;
         tok.column = newCol ;
         lastLine.addElement(tok) ;
      }

    public void addLine() 
      { /*******************************************************************
        * The new line is set to an empty vector.                          *
        *******************************************************************/
        tokens.addElement(new Vector()) ;
      }

    public void normalize() 
      { /*******************************************************************
        * Remove empty lines at beginning and end of tokens.               *
        *******************************************************************/
        while (    (tokens.size() > 0)
                   /********************************************************
                   * I don't think we should ever get an empty             *
                   * expression, but we'll check just in case.             *
                   ********************************************************/
                && (((Vector) tokens.elementAt(0)).size() == 0 )
              )
          { tokens.removeElementAt(0) ;
          } ;

        while (    (tokens.size() > 0)
                   /********************************************************
                   * I don't think we should ever get an empty             *
                   * expression, but we'll check just in case.             *
                   ********************************************************/
                && (((Vector) tokens.elementAt(tokens.size()-1)).size() == 0)
              )
          { tokens.removeElementAt(tokens.size()-1) ;
          } ;

        /*******************************************************************
        * Set minCol to minimum column number.                             *
        *******************************************************************/
        int minCol = 999999 ;
        int i = 0 ;
        
        while (i < tokens.size())
          { if ( ((Vector) tokens.elementAt(i)).size() > 0 )
              { TLAToken tok = 
                   (TLAToken) ((Vector) tokens.elementAt(i)).elementAt(0);
                if (tok.column < minCol) {minCol = tok.column;} ;
              }
            i = i + 1;
          };

        /*******************************************************************
        * Subtract minCol from tok.column for all tokens tok.              *
        *******************************************************************/
        i = 0;
        while (i < tokens.size())
          { int j = 0 ;
            Vector curLine = (Vector) tokens.elementAt(i) ;
            while (j < curLine.size())
              { TLAToken tok = (TLAToken) curLine.elementAt(j) ;
                tok.column = tok.column - minCol ;
                j = j + 1;
              };
            i = i + 1;
          } ;

        /*******************************************************************
        * Compute anchorTokens and anchorTokCol.                           *
        *                                                                  *
        * Loop with index i through all lines.                             *
        *******************************************************************/
        anchorTokens = new TLAToken[tokens.size()];
        anchorTokCol = new int[tokens.size()];
        i = 0 ;
        while (i < tokens.size())
          { Vector curLine = (Vector) tokens.elementAt(i) ;
            if (curLine.size() > 0)
              { int curLineFirstCol = 
                      ((TLAToken) curLine.elementAt(0)).column;
                /***********************************************************
                * Loop backwards with loop index j through lines (i-1) ->  *
                * 0, exiting when anchor line found.                       *
                ***********************************************************/
                int j = i-1 ;
                boolean lineNotFound = true ;
                while ((j >= 0) && lineNotFound)
                  { Vector ancLine = (Vector) tokens.elementAt(j) ;
                    if (   (ancLine.size() > 0)
                        && ( ((TLAToken) ancLine.elementAt(0)).column
                                <= curLineFirstCol
                           ) )
                      { /***************************************************
                        * This line contains the anchor token.             *
                        ***************************************************/
                        lineNotFound = false;

                        /***************************************************
                        * Loop indexed by k starting at 1 through tokens   *
                        * on ancLine until reaching end or a token to the  *
                        * right of curLineFirstCol.                        *
                        ***************************************************/
                        int k = 0 ;             
                        while (   (k+1 < ancLine.size()) 
                               && ( ((TLAToken) 
                                       ancLine.elementAt(k+1)).column
                                         <= curLineFirstCol)
                              )
                          { k = k+1 ;} ;

                        TLAToken tok = (TLAToken) ancLine.elementAt(k) ;
                        anchorTokens[i] = tok ;
                        anchorTokCol[i] = tok.column ;
                       }; //END if
                    j = j - 1;
                  }; //END while j
              };
            i = i + 1;
          }; //END while i      
      } //END normalize

    public void renormalize() throws TLAExprException
      /*********************************************************************
      * Used to renormalize the expression so anchorTokCol[i] equals the   *
      * actual column of the anchorTokens[i].  It should be called every   *
      * time new tokens have been inserted into the expression.            *
      *                                                                    *
      * This is done as follows.  For each i from 0 to the maximum line    *
      * number, if the anchor token of line i has moved k tokens to the    *
      * right, then anchorTokCol[i] and the columns of every token in      *
      * line i are incremented by k.                                       *
      *********************************************************************/
      { int i = 0 ;
        while (i < tokens.size())
          { if (anchorTokens[i] != null)
              { Vector line = (Vector) tokens.elementAt(i) ;
                int k = anchorTokens[i].column - anchorTokCol[i] ;
                anchorTokCol[i] = anchorTokens[i].column ;
                if (k < 0)
                  { throw new TLAExprException(
                     "TLAExpr.renormalize() found anchor has moved to left.");
                  } ;
                int j = 0 ;
                while (j < line.size())
                  { TLAToken tok = (TLAToken) line.elementAt(j) ;
                    tok.column = tok.column + k ;
                    j = j + 1;
                  } ;
               } ;
            i = i + 1;
          }
      }
      
    public Vector toStringVector()
      { Vector result = new Vector(tokens.size()) ;
        int i = 0 ;
        while (i < tokens.size())
          { Vector curTokLine = (Vector) tokens.elementAt(i) ;
            String curString = "" ;
            TLAToken curAncTok = anchorTokens[i] ;
            int      curAncCol = anchorTokCol[i] ; 
            if (curAncTok != null)
              {curString = SpacesString(curAncTok.column - curAncCol) ;} 

            TLAToken curTok = null ;
            TLAToken lastTok = null ;
            int j = 0 ;
            while (j < curTokLine.size())
              { curTok = (TLAToken) curTokLine.elementAt(j);
                if (j == 0)
                  {curString = curString + SpacesString(curTok.column) ; }
                else
                  {curString = 
                     curString +
                     SpacesString( curTok.column - lastTok.column
                                     - lastTok.getWidth()) ;}
                /***********************************************************
                * Need to add the quotes for a string token.               *
                ***********************************************************/
                if (curTok.type == TLAToken.STRING)
                     {curString = curString + "\"" + curTok.string + "\""; }
                else { curString = curString + curTok.string ; };
                lastTok = curTok ;
                j = j + 1;
              }
            result.addElement(curString) ;
            i = i + 1;
          }
        return result;
      }

    public String toString()
      { String result = "<< " ;
        int i = 0;
        boolean nonempty = false ;
        while (i < tokens.size() )
         { if (i > 0)
             { result = result + "\n" ; } ;
           Vector curLine = (Vector) tokens.elementAt(i);
           int j = 0 ;
           while (j < curLine.size())
             { if (nonempty)
                 { result = result + ", " ; } ;
               nonempty = true ;
               TLAToken tok = (TLAToken) curLine.elementAt(j) ;
               if (tok.type == TLAToken.STRING)
                 { result = result + "\"\\\"\", \"" + tok.string 
                                + "\", \"\\\"\"" ;
                 }
               else if (tok.string.charAt(0) == '\\')
                 { result = result + "\"\\" + tok.string + "\""; }
               else if (tok.string.equals("/\\"))
                  { result = result + "\"" + "/\\\\" + "\""; }
               else
                 { result = result + "\"" + tok.string + "\""; }
               j = j + 1 ;
             }
           i = i + 1;
         }
        return result + " >>" ;
      }

   public void appendExpr(Vector expr, int spaces) throws UnrecoverableException
     { 
       // DEADCODE
       throw new UnrecoverableException("appendExpr not yet implemented");
     }


/***************************************************************************
*        METHODS FOR SEARCHING AND SUBSTITUTING IN EXPRESSIONS             *
*                                                                          *
* The tokens field of a TLAExpr is a vector of lines, where a line is a    *
* vector of tokens.  The "Java coordinates" of a token in the expression   *
* is a pair (ln, itm) such that the token is item number itm in line       *
* number ln, where the numbering of lines and items starts at 0.  Note     *
* that the first token of an expression always has coordinates (0, 0).     *
* Java coordinates are passed as arguments and returned as values as       *
* IntPair objects.                                                         *
***************************************************************************/
    public TLAExpr cloneAndNormalize() 
      /*********************************************************************
      * Creates a clone of the current TLAExpr by cloning all the tokens   *
      * and then calling normalize to compute anchorTokens and             *
      * anchorTokCol.                                                      *
      *********************************************************************/
      { TLAExpr result = new TLAExpr() ;
        result.tokens = new Vector() ;
        int i = 0 ;
        while (i < this.tokens.size() )
          { Vector newline = new Vector() ;
            Vector line = (Vector) this.tokens.elementAt(i) ;
            int j = 0 ;
            while (j < line.size())
              { newline.add(((TLAToken) line.elementAt(j)).Clone()) ;
                j = j + 1 ;
              } ;
            result.tokens.add(newline) ;
            i = i + 1 ;
          } ;
        result.normalize() ;
        return result ;
      }

    public void prepend(TLAExpr expr, int spaces) throws TLAExprException 
      /*********************************************************************
      * Prepends the expression expr to the front of the current           *
      * expression, leaving `spaces' number of spaces between the last     *
      * token of expr and the first token of the current expression.       *
      *********************************************************************/
      { /*******************************************************************
        * Prepend all but the last line of expr to the current expression. *
        *******************************************************************/
        int i = 0 ;
        while (i < expr.tokens.size()-1)
          { this.tokens.add(i, expr.tokens.elementAt(i)) ;
            i = i + 1 ;
          } ;
        /*******************************************************************
        * Set exprLine to the last line of expr and thisLine to what was   *
        * the first line of the current expression.                        *
        *******************************************************************/
        Vector exprLine = (Vector) expr.tokens.elementAt(i) ;
        Vector thisLine = (Vector) this.tokens.elementAt(i) ;

        /*******************************************************************
        * Increment the columns of the tokens in thisLine.                 *
        *******************************************************************/
        TLAToken tok = (TLAToken) exprLine.lastElement() ;
        int incr = tok.column + tok.getWidth() + spaces ;
        int j = 0 ;
        while (j < thisLine.size())
          { tok = (TLAToken) thisLine.elementAt(j) ;
            tok.column = tok.column + incr ;
            j = j + 1 ;
          } ;

        /*******************************************************************
        * Prepend the last line of expr to the first line of this          *
        * expression.                                                      *
        *******************************************************************/
        j = 0 ;
        while (j < exprLine.size())
          { thisLine.add(j, exprLine.elementAt(j)) ;
            j = j + 1 ;
          } ;        

        /*******************************************************************
        * Modify anchorTokens and anchorTokCol.                            *
        *******************************************************************/
        TLAToken[] newAToks = new TLAToken[this.tokens.size()] ;
        int[]      newATCol = new int[this.tokens.size()] ;

        j = 0 ;
        while (j < expr.tokens.size())
          { newAToks[j] = expr.anchorTokens[j] ;
            newATCol[j] = expr.anchorTokCol[j] ;
            j = j + 1 ;
          } ;

        while (j < this.tokens.size())
           { newAToks[j] = this.anchorTokens[j - expr.tokens.size() + 1] ;
             newATCol[j] = this.anchorTokCol[j - expr.tokens.size() + 1] ;
             j = j + 1 ;
          } ;
        this.anchorTokens = newAToks ;
        this.anchorTokCol = newATCol ;
        
        this.renormalize() ;
        return ;
      }
        
    public void insertNewToken(String str, IntPair coord) throws TLAExprException
      /*********************************************************************
      * Inserts a new token into expr right after the token with Java      *
      * coordinates coord.  The token has string str and some type other   *
      * than STRING.                                                       *
      *********************************************************************/
      { int lineNum = coord.one ;
        int tokNum  = coord.two ;
        if (lineNum >= tokens.size())
          { PcalDebug.ReportBug("insertNewToken called with lineNum too big");}
        Vector curLine = (Vector) tokens.elementAt(lineNum) ;

        if (tokNum >= curLine.size())
          { PcalDebug.ReportBug("insertNewToken called with tokNum too big"); }
    
        TLAToken curTok = ((TLAToken) curLine.elementAt(tokNum)) ;

        curLine.insertElementAt(new 
                                  TLAToken(str, 
                                           curTok.column + curTok.getWidth(), 
                                           TLAToken.BUILTIN),
                                tokNum + 1);

        /*******************************************************************
        * Increment the columns of later tokens in the line by the length  *
        * of str.                                                          *
        *******************************************************************/
        int i = tokNum + 2;
        while (i < curLine.size())
          { ((TLAToken) curLine.elementAt(i)).column =
              ((TLAToken) curLine.elementAt(i)).column + str.length() ;
            i = i + 1;
          };
        this.renormalize() ;
      }  

    public static Vector SeqSubstituteForAll(Vector expVec, // of TLAExpr
                                             Vector exprs,  // of TLAExpr
                                             Vector strs) throws TLAExprException   // of String
      /*********************************************************************
      * Produces a vector of new expressions obtained by cloning each      *
      * expression in expVec and then applying substituteForAll(expres,    *
      * strs) to the clone.                                                *
      *********************************************************************/
      { Vector result = new Vector() ;
        int i = 0 ;
        while (i < expVec.size())
          { TLAExpr e = ((TLAExpr) expVec.elementAt(i)).cloneAndNormalize() ;
            e.substituteForAll(exprs, strs) ;
            result.add(e) ;
            i = i + 1 ;
          } ;
        return result ;
      }      

   public void substituteForAll( Vector exprs , // of TLAExpr
                                  Vector strs    // of String
                                ) throws TLAExprException
      { substituteForAll(exprs, strs, true); }

    public void substituteForAll( Vector exprs , // of TLAExpr
                                  Vector strs ,  // of String
                                  boolean parenthesize
                                ) throws TLAExprException
      /*********************************************************************
      * Substitute each of the expressions in exprs for the corresponding  *
      * string in strs.  (The vectors must have the same lengths.)         *
      * If parenthesize = true, then parentheses are put around the        *
      * substituted string unless it or the current expression consists    *
      * of just on token.                                                  *
      *********************************************************************/
      { int i = 0 ;
        while (i < exprs.size())
          { TLAExpr exp = (TLAExpr) exprs.elementAt(i) ;
            String  st  = (String)  strs.elementAt(i) ;
            substituteFor(exp, st, parenthesize) ;
            i = i + 1;
          };
        return;
      }      

     public void substituteFor(TLAExpr expr, String id, boolean parenthesize) throws TLAExprException
      /*********************************************************************
      * Substitutes expression expr for all tokens in the current          *
      * expression representing the identifier id -- that is, instances    *
      * in which id does not represent the name of a record field.         *
      * If parenthesize = true, then parentheses are put around the        *
      * substituted string unless it or the current expression consists    *
      * of just on token.                                                  *
      *********************************************************************/
      { IntPair next =  new IntPair(0, 0) ;
        while (next != null)
          { next = this.findNextInstanceIn(id, next) ;
            if (next != null)
                { next = this.substituteAt(expr, next, parenthesize) ;
              }
          }
      }


      public IntPair substituteAt(TLAExpr expr, IntPair coord, boolean par) throws TLAExprException 
      /*********************************************************************
      * Replaces the token tok with coordinates coord in the current       *
      * expression with the expression expr (adding parentheses when       *
      * needed if par = true), and return the coordinates of the token     *
      * immediately past the substituted expression (or null if the        *
      * substitution was for the last token).  The trick is to do this is  *
      * a way that preserves the alignment information.  In particular,    *
      * we have to be concerned with the possibility that token tok might  *
      * be an anchor token.  If the current expression consists of a       *
      * single token, then we just replace its fields the fields obtained  *
      * by cloning expr.  Otherwise, there are two cases.                  *
      *                                                                    *
      * Case 1: expr consists of a single token etok.                      *
      *    In this case, the `string' and `type' fields of tok are         *
      *    set to the corresponding fields of etok, and the                *
      *    remainder tokens on the current line are shifted                *
      *    to the new string has more characters than the                  *
      *    original.                                                       *
      *                                                                    *
      * Case 2: expr consists of multiple tokens.                          *
      *    In this case, tok is changed to "(", and copies of the tokens   *
      *    of expr followed by a ")" token are inserted into the current   *
      *    expression, creating one new line for every line of expr other  *
      *    than the first.  The column of each token from expr is          *
      *    incremented by 1 plus the column number of tok.  The tokens     *
      *    from the current expression that follow on the same line as the *
      *    last line of the newly inserted tokens are incremented by the   *
      *    appropriate amount to shift them to the right of the inserted   *
      *    tokens.                                                         *
      *********************************************************************/
      { /*******************************************************************
        * First handle of the case when current expression has a single    *
        * token.                                                           *
        *******************************************************************/
        if (this.isOneToken())
          { TLAExpr cloned = expr.cloneAndNormalize() ;
            this.tokens = cloned.tokens ;
            this.anchorTokens = cloned.anchorTokens ;
            this.anchorTokCol = cloned.anchorTokCol ;
            return null ;
          } ;

        /*******************************************************************
        * Set                                                              *
        *                                                                  *
        *    tok = the token being substituted for,                        *
        *    spaces = number of spaces between tok and token to its right, *
        *             or 0 if tok at end of line.                          *
        *    restOfLine = a vector of the tokens to the right of tok,      *
        *                                                                  *
        * and delete tokens to right of tok from expr.                     *
        *******************************************************************/
        TLAToken tok = this.tokenAt(coord) ;
        Vector tokLine = (Vector) this.tokens.elementAt(coord.one) ;
        int spaces = 0 ;
        if (coord.two + 1 < tokLine.size())
          { TLAToken nextTok = (TLAToken) tokLine.elementAt(coord.two + 1) ;
            spaces = nextTok.column - (tok.column + tok.getWidth()) ;
          } ;
        Vector restOfLine = new Vector() ;
        while (coord.two + 1 < tokLine.size())
          { restOfLine.add(tokLine.elementAt(coord.two + 1)) ;
            tokLine.remove(coord.two + 1) ;
          }

        /*******************************************************************
        * curLine will be set to the line number and line to the line at   *
        * the end of which the tokens in restOfLine will be appended.      *
        *******************************************************************/
        int curLine = coord.one ;
        Vector line = (Vector) this.tokens.elementAt(curLine) ;        
        /*******************************************************************
        * Insert the new tokens into the expression.                       *
        *******************************************************************/
        if (    (expr.tokens.size() == 1)
             && ( ((Vector) expr.tokens.elementAt(0)).size() == 1)
           )
          { /***************************************************************
            * There is a single token etok.                                *
            ***************************************************************/
            TLAToken etok = 
                (TLAToken) ((Vector) expr.tokens.elementAt(0)).elementAt(0) ;
            tok.string = etok.string ;
            tok.type   = etok.type ;
          } 
        else
          { /***************************************************************
            * There are multiple tokens.                                   *
            *                                                              *
            * Replace tok by "(" token if par = true, and set indent to    *
            * the amount to indent the first line of inserted tokens.      *
            ***************************************************************/
            int indent = ((par) ?  1 : 0) + tok.column ; 

            /***************************************************************
            * Set doInsert to true iff the token being substituted for     *
            * must be replaced with the first token of the expression,     *
            * otherwise set it to false and substitute a "(" for it.       *
            ***************************************************************/
            boolean doInsert = true;
            if (par) {
                tok.string = "(" ;
                tok.type   = TLAToken.BUILTIN ;
                doInsert = false ;
            }
            int i = 0 ;
            TLAExpr newExpr = expr.cloneAndNormalize() ;
            while (i < newExpr.tokens.size())
              { Vector eline = (Vector) newExpr.tokens.elementAt(i) ;
                int j = 0 ;
                while (j < eline.size())
                  { TLAToken nextTok = 
                               (TLAToken) eline.elementAt(j) ;
                    nextTok.column = nextTok.column + indent ;
                    if (doInsert) {
                        tok.string = nextTok.string ;
                        tok.type = nextTok.type ;
                        doInsert = false ; 
                    }
                    else line.add(nextTok) ;
                    j = j + 1 ;
                  }
                i = i + 1;
                if (i < newExpr.tokens.size())
                  { /*******************************************************
                    * Increment curLine, insert a new empty line into      *
                    * expr at this position, insert                        *
                    * newExpr.anchorTokens[curLine] into                   *
                    * this.anchorTokens as item i, and similarly for       *
                    * anchorTokCol.                                        *
                    *******************************************************/
                    indent = 0 ;
                    curLine = curLine + 1 ;
                    this.tokens.insertElementAt(new Vector() , curLine) ;
                    line = (Vector) this.tokens.elementAt(curLine) ;
                    TLAToken[] aTok  = new TLAToken[this.tokens.size()] ;
                    int[]      aTCol = new int[this.tokens.size()] ;
                    int k = 0 ;
                    while (k < this.tokens.size())
                      { if (k < curLine)
                          { aTok[k]  = this.anchorTokens[k];
                            aTCol[k] = this.anchorTokCol[k];
                          }
                        else if (k == curLine)
                          { aTok[k]  = newExpr.anchorTokens[i];
                            aTCol[k] = newExpr.anchorTokCol[i];
                          }
                        else
                          { aTok[k]  = this.anchorTokens[k-1];
                            aTCol[k] = this.anchorTokCol[k-1];
                          }
                        k = k + 1;
                      } ;
                     this.anchorTokens = aTok ;
                     this.anchorTokCol = aTCol ;
                  } ;
              } ;
            TLAToken lastTok = (TLAToken) line.elementAt(line.size() - 1) ;
            if (par) {
                TLAToken rParen =
                    new TLAToken(")",
                                 lastTok.column + lastTok.getWidth(),
                                 TLAToken.BUILTIN );
                line.add(rParen) ;
            }
          } 

        IntPair result = new IntPair(curLine, line.size()-1);
        /*******************************************************************
        * Put the tokens from restOfLine back into the expression.         *
        *******************************************************************/
        if (restOfLine.size() > 0)
          { TLAToken prevTok  = (TLAToken) line.elementAt(line.size() - 1) ;
            TLAToken firstTok = (TLAToken) restOfLine.elementAt(0);
            int indent = prevTok.column + prevTok.getWidth() 
                           + spaces - firstTok.column ;
            int i = 0 ;
            while (i < restOfLine.size())
              { TLAToken oldTok = (TLAToken) restOfLine.elementAt(i) ;
// Correction made 25 Aug 2005.
// For some reason I no longer understand, I was replacing the original
// tokens with new ones.  This was wrong because any anchorToken that
// pointed to one of those tokens was now pointing to the wrong
// TLAToken object.  Here's the bad code:
//
//                TLAToken newTok = new TLAToken(oldTok.string,
//                                               oldTok.column + indent ,
//                                               oldTok.type) ;
//                line.add(newTok) ;
                oldTok.column = oldTok.column + indent ;
                line.add(oldTok) ;
                i = i + 1 ;
              }
          } ;
        this.renormalize() ;
        return this.stepCoord(result, 1);
      }     

    public IntPair findNextInstanceIn(String  id,
                                      IntPair start)
      /*********************************************************************
      * If expr is a TLAExpr, then expr.findNextInstanceIn(id, start)      *
      * returns the Java coordinates of the first token with Java          *
      * coordinates at or after "start" with string id that represents an  *
      * identifier.  It ignores tokens with string id that represent       *
      * record labels.  However, in certain exceptional cases, it will     *
      * ignore an instance that binds the identifier id in a quantified    *
      * expression--for example, in the expression "\E x, id : ...".       *
      * This method should therefore not be used in the case when id       *
      * could legally be a bound identifier of a quantified expression.    *
      *                                                                    *
      * The search is performed as if the first token of the expression    *
      * were the one with Java coordinates `start'.  This means that the   *
      * method will mistakenly return `start' if it is the Java            *
      * coordinates of a record label.  For example, if the method is      *
      * invoked for the expression "[id |-> 17]" with `start' equal to     *
      * the coordinates of the token id, then the method will return       *
      * `start', even though id does not represent an identifier in the    *
      * whole expression.                                                  *
      *                                                                    *
      * The method regards an id to be a record label iff it appears in    *
      * the following contexts:                                            *
      *                                                                    *
      *    . id                                                            *
      *    [ id :                                                          *
      *    , id :                                                          *
      *    [ id |->                                                        *
      *    , id :                                                          *
      *                                                                    *
      * I believe this works except that it misidentifies id as a record   *
      * label when it appears as a bound identifier in an unbounded        *
      * quantifier expression such as                                      *
      *                                                                    *
      *    \E x, id : ...                                                  *
      *********************************************************************/
      { IntPair result = new IntPair(start.one, start.two) ;
        if (this.isEmpty()) { result = null ; } ;
        while (result != null)
          { TLAToken tok = this.tokenAt(result) ;
            if (tok.type == TLAToken.STRING)
              { result = this.stepCoord(result, 1) ;
              }
            else if (tok.string.equals("."))
                   { result = this.stepCoord(result, 2) ;
                   }
            else if (    (    tok.string.equals("[")
                           || tok.string.equals(",") 
                         )
                      && (this.stepCoord(result, 2) != null)
                      && (this.tokenAt(this.stepCoord
                               (result, 2)).type != TLAToken.STRING )
                      && (    this.tokenAt(this.stepCoord
                               (result, 2)).string.equals(":") 
                           || this.tokenAt(this.stepCoord
                               (result, 2)).string.equals("|->") 
                         )
                     )
                   { result = this.stepCoord(result, 3); }
            else if (tok.string.equals(id))
                   { return result ;} 
            else { result = this.stepCoord(result, 1); }
            
          }
        return null ;
      }

   public TLAToken tokenAt(IntPair coord)
     /**********************************************************************
     * exp.tokenAt(coord) is the TLAToken in TLAExpr exp with Java         *
     * coordinates coord.                                                  *
     **********************************************************************/
     { return  (TLAToken) 
                 ((Vector) 
                     this.tokens.elementAt(coord.one)).elementAt(coord.two) ;
     }

   public IntPair stepCoord(IntPair coord, int incr) 
     /**********************************************************************
     * exp.stepCoord(coord, incr) returns the Java coordinates of the      *
     * token in exp that is incr tokens past the one with Java             *
     * coordinates coord.  If there is no such token, then it returns      *
     * null.                                                               *
     **********************************************************************/
     { /********************************************************************
       * Check that coord is a valid coordinate pair.                      *
       ********************************************************************/
       if (tokens.size() <= coord.one)
         { PcalDebug.ReportBug(
                "TLAExpr.StepCoord called with line too big") ; } ;
       Vector line = (Vector) tokens.elementAt(coord.one) ;
       if (line.size() <= coord.two)
         {PcalDebug.ReportBug(
                 "TLAExpr.StepCoord called with col too big") ; } ;

       IntPair result = new IntPair(coord.one, coord.two) ;
       int i = 0 ;
       while (i < incr)
         { result.two = result.two + 1 ;
           if (line.size() == result.two)
             { result.two = 0 ;
               result.one = result.one + 1 ;
               while (   (result.one < tokens.size())
                      && ( ((Vector) tokens.elementAt(result.one )).size()
                              == 0) )
                 { result.one = result.one + 1 ;
                 } ;
               if (result.one == tokens.size())
                 { return null ; } ;
               line = (Vector) tokens.elementAt(result.one) ;
             }
           i = i + 1;
         } ;
       return result ;
     }

   public boolean isEmpty()
     {return    (tokens == null)
             || (tokens.size() == 0) ;
     }

   public boolean isOneToken()
     {return    (! this.isEmpty())
             && (tokens.size() == 1)
             && ( ((Vector) tokens.elementAt(0)).size() == 1 ) ;
     }
  /***************** private and debugging methods *********************/

   private static String SpacesString(int n)
    /***********************************************************************
    * A string of n spaces.                                                *
    ***********************************************************************/
    { int i = 0 ;
      String result = "" ;
      if (i < 0) {PcalDebug.ReportBug(
                    "SpacesString called with negative argument");}
      while (i < n)
       { result = result + " ";
         i = i + 1;
       }
      return result;
    }




    /************************************************************************
    * For debugging, the following prints a TLAExpr with an indicated name. *
    ************************************************************************/
    public void print(String name) 
      { PcalDebug.print2DVector(tokens, name + ".tokens") ;
        PcalDebug.printObjectArray(anchorTokens, name + ".anchorTokens") ;
        PcalDebug.printIntArray(anchorTokCol, name + ".anchorTokCol") ;
      }

/***************************************************************************
* Appending Vectors:                                                       *
*                                                                          *
* For any distinct vectors v and v2, the method v.addAll(v2)               *
* apparently appends v2 to the end of v, and returns true iff this v2 is   *
* non-empty, so this changes v.                                            *
***************************************************************************/

  }


/* last modified on Fri 31 Aug 2007 at 14:03:38 PST by lamport */
