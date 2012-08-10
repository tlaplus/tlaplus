// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS TokenizeComment                                                    *
*                                                                          *
* This class contains a a single method, Tokenize, that takes as argument  *
* a multiline comment represented as a Vector whose elements are strings.  *
* Its result is an array of arrays of CTokens obtained by tokenizing the   *
* comment.  Each element of the vector produces one row of the array.      *
*                                                                          *
* Note: in formatting comments, we don't treat PlusCal built-in tokens     *
* specially because they are mostly strings like "if", "with", and "while" *
* that are very common English words.  As a result, we don't try to format *
* PlusCal code as such in comments.                                        *
*                                                                          *
* The tokenizing algorithm is described below.  The description has the    *
* following BNF syntax:                                                    *
*                                                                          *
*    <Description> ::=                                                     *
*        <State_Action> | <State_Action> <Description>                     *
*                                                                          *
*    <State_Action>    ::=  <State_Name> ":" <Action_Sequence>             *
*                                                                          *
*    <Action_Sequence> ::=  <Action> | <Action> <Action_Sequence>          *
*                                                                          *
*    <Action> ::=                                                          *
*         <Precondition> <Step_Sequence> "-->" <State_Name>                *
*                                                                          *
*    <Step_Sequence> ::= <Step> | <Step> ";" <StepSequence>                *
*                                                                          *
* The algorithm has a current state, which is initially START. When in     *
* a state S, the algorithm executes the <Action_Sequence> for the          *
* <State_Action> whose <State_Name> is S. It executes an                   *
* <Action_Sequence> by going through its actions in order until it         *
* finds one whose <Precondition> is true.  It then executes the <Step>s    *
* in that <Action>'s <Step_Sequence>, and then sets the current state      *
* to the <Action>'s <State_Name>.  However, the special <State_Name>s      *
* DONE and ERROR indicate that the algorithm is finished, either           *
* normally or with an error.                                               *
*                                                                          *
* The algorithm uses the following variables:                              *
*                                                                          *
*    token :    The part of the token found so far.                        *
*                                                                          *
*    nextChar : The next character from the input stream                   *
*                                                                          *
*    inDQuote : True iff left double-quote has been encountered            *
*               and the matching right double-quote has not                *
*               been.                                                      *
*    inSQuote : True iff a left single-quote has been encountered          *
*               and the matching right single-quote has not                *
*               been.                                                      *
*                                                                          *
* A <Precondition> has the form [exp], where exp is an ordinary            *
* expression, except the following conventions are used in it:             *
*                                                                          *
*   (S) asserts that nextChar equals S if S is a character, or             *
*     that nextChar is an element of S if S is a set of characters.        *
*     LegalStringChar is the set of all legal non-escaped characters       *
*     in a TLA+ string.                                                    *
*                                                                          *
*   token+ is the string obtained by appending nextChar to token.          *
*                                                                          *
*   BuiltIns is the set of all strings that are recognized by              *
*     TLA+ as operators or keywords.                                       *
*                                                                          *
*   BuiltInPrefix is the set of prefixes of all strings in                 *
*     BuiltIns except all-letter strings or strings consisting             *
*     of a "\\" (a backslash) followed by a sequence of letters.           *
*                                                                          *
*   OTHER equals TRUE.                                                     *
*                                                                          *
* I write (S) instead of [(S)].                                            *
*                                                                          *
* The following notation for steps is used.                                *
*                                                                          *
*   + means to append nextChar to token and set nextChar to the            *
*     next character in the input stream.                                  *
*                                                                          *
*   - means to set nextChar to the next character in the input             *
*     stream.                                                              *
*                                                                          *
*   CTokenOut(type) outputs  token as a CToken of the indicated            *
*   type and resets token to the empty string.                             *
*                                                                          *
* Here is the algorithm.                                                   *
*                                                                          *
* START:                                                                   *
*   (Space_Char)        -                      --> START                   *
*   (Letter)            +                      --> ID                      *
*   (Digit)             +                      --> NUM_OR_ID               *
*   ("\n")              -                      --> START                   *
*   ("\\")              +                      --> BS                      *
*   (\in RepeatChars)   repChar = nextChar; +                              *
*                       repMin  = min repetition number                    *
*                                 of nextChar;                             *
*                                              --> REPEAT_CHAR             *
*   ("\"" /\ ~inDQuote) -                      --> STRING                  *
*   ("\"")              +                      --> RIGHT_DQUOTE            *
*   ("`")               +                      --> LEFT_SQUOTE             *
*   ("'" /\ inSQuote)   - ; inSQuote = false   --> START                   *
*   ("'")               +                      --> RIGHT_SQUOTE            *
*   (BuiltInPrefix)     +                      --> BUILT_IN                *
*   ("\t")                                     --> DONE                    *
*   [OTHER]             + ; CTokenOut(OTHER)   --> START                   *
*                                                                          *
* ID:                                                                      *
*   [token = "WF_" or "SF_"]  CTokenOut(BUILTIN)    --> START              *
*   (Letter or Digit)         +                     --> ID                 *
*   [token \in BuiltIns]      CTokenOut(BUILTIN)    --> START              *
*   [OTHER]                   CTokenOut(IDENT)      --> START              *
*                                                                          *
* NUM_OR_ID:                                                               *
*   (Digit)   +                  --> NUM_OR_ID                             *
*   (Letter)  +                  --> ID                                    *
*   [OTHER]   CTokenOut(NUMBER)  --> START                                 *
*                                                                          *
* BS:                                                                      *
*   ("b", "B", "o", "O", "h", or "H") +                --> NUM_OR_BI       *
*   (Letter)                                           --> BSBUILT_IN      *
*   [OTHER]                                            --> BUILT_IN        *
*                                                                          *
* NUM_OR_BI                                                                *
*   (Digit)   --> NUM                                                      *
*   [OTHER]   --> BSBUILT_IN                                               *
*                                                                          *
* NUM:                                                                     *
*   (Digit)  +                       --> NUM                               *
*   (Letter /\ token[1] != '\')  +   --> ID                                *
*   [OTHER]  CTokenOut(NUMBER)       --> START                             *
*                                                                          *
* BSBUILT_IN:                                                              *
*   (Letter)              +                   --> BSBUILT_IN               *
*   [token \in BuiltIns]  CTokenOut(BUILTIN)  --> START                    *
*   [OTHER]               CTokenOut(OTHER)    --> START                    *
*                                                                          *
* BUILT_IN:                                                                *
*   [token+ \in BuiltInPrefix]  +                  --> BUILT_IN            *
*   [OTHER]   while (token \notin BuiltIn)                                 *
*               {move last char in token back                              *
*                to the CharReader};                                       *
*             CTokenOut(BUILTIN)                   --> START               *
*                                                                          *
* REPEAT_CHAR:                                                             *
*   (repChar)   +                                  --> REPEAT_CHAR         *
*   [Len(token) \geq getRepeatCharMin(repChar)]                            *
*                  CTokenOut(REP_CHAR)             --> START               *
*   [OTHER]                                        --> BUILT_IN            *
*                                                                          *
* (**********************************************************)             *
* (* Note that we leave in the string the "\" of an escape  *)             *
* (* character like "\n".                                   *)             *
* (**********************************************************)             *
* STRING:                                                                  *
*   ("\\")             +                           --> ESC_STRING          *
*   ("\"" /\ (token in stringHashTable \/ inSQuote)                        *
*                   (*****************************************)            *
*                   (* Note: `\/ inSQuote' added 30 Jan 2001 *)
*                   (*****************************************)            *
*                     - ; CTokenOut(STRING)         --> START              *
*   (LegalStringChar)  +                           --> STRING              *
*   [OTHER]  --> LEFT_DQUOTE                                               *
*                                                                          *
* ESC_STRING:                                                              *
*   ("\"", "\\", "t", "n", "f", or "r")  +        --> STRING               *
*   [OTHER] --> LEFT_DQUOTE                                                *
*                                                                          *
* LEFT_DQUOTE:                                                             *
*   [OTHER] Backspace(Len(token)+1); token = "\"";                         *
*           CTokenOut(LEFT_DQUOTE); inDQuote = true --> START              *
*                                                                          *
* RIGHT_DQUOTE:                                                            *
*   [OTHER] CTokenOut(RIGHT_DQUOTE); inDQuote = false --> START            *
*                                                                          *
* LEFT_SQUOTE:                                                             *
*   (`)  + CTokenOut(OTHER);                --> START                      *
*   (^)  - ; token = "" ;                   --> TEX                        *
*   (~)  - ; token = "" ;                   --> THROW_AWAY                 *
*   (.)  - ; token = "  "                   --> VERB                       *
*       (************************************************************)     *
*       (* Note: we replace the "`." by spaces in first VERB token. *)     *
*       (************************************************************)     *
*   [OTHER]  token = ""; inSQuote = true    --> START                      *
*         (************************************************************)   *
*         (* Note: we add a hack here to decrement col so, if there   *)   *
*         (* is no space between the "`" and the next token, then the *)   *
*         (* starting column of that token is the column of the "`".  *)   *
*         (* This gets alignments right if a line in a multi-line     *)   *
*         (* comment begins with `token'.  However, it introduces the *)   *
*         (* following bug: if the ' is immediately followed by a     *)   *
*         (* character, as in "`token'.", then it will appear as if   *)   *
*         (* there is a space before the ".", so TLATeX inserts a     *)   *
*         (* spurious space in the output.  One way to fix this is to *)   *
*         (* add 1 to the length of a token immediately following a ` *)   *
*         (* and add 1 to the length of a token immediately preceding *)   *
*         (* a '.  The latter requires some kludgery.                 *)   *
*         (************************************************************)   *
*                                                                          *
* RIGHT_SQUOTE:                                                            *
*   (')      + ; CTokenOut(OTHER)   --> START                              *
*   [OTHER]                         --> BUILT_IN                           *
*                                                                          *
* TEX:                                                                     *
*   (^)      -                        ---> TEX_CARET                       *
*   ("\n")   IF token = ""                                                 *
*              THEN token = " " ;                                          *
*            CTokenOut(TEX);                                               *
*            token = ""               ---> TEX                             *
*   ("\t")   IF token nonblank                                             *
*              THEN CTokenOut(TEX)    ---> DONE                            *
*   [OTHER]  +                        ---> TEX                             *
*                                                                          *
* TEX_CARET :                                                              *
*   (')     - ; IF token nonblank                                          *
*                 THEN CTokenOut(TEX)     ---> START                       *
*   [OTHER] token = token + ".";          ---> TEX                         *
*                                                                          *
* THROW_AWAY:                                                              *
*   (~)      -    ---> THROW_AWAY_TILDE                                    *
*   (\n)     -    ---> THROW_AWAY                                          *
*   ("\t")   -    ---> DONE                                                *
*   [OTHER]  -    ---> THROW_AWAY                                          *
*                                                                          *
* THROW_AWAY_TILDE:                                                        *
*   (')      -    ---> START                                               *
*   [OTHER]  -    ---> THROW_AWAY                                          *
*                                                                          *
* VERB:                                                                    *
*   (.)      -                        ---> VERB_DOT                        *
*   ("\n")   IF token nonblank                                             *
*              THEN CTokenOut(VERB);                                       *
*            token = ""               ---> VERB                            *
*   ("\t")   IF token nonblank                                             *
*              THEN CTokenOut(VERB)   ---> DONE                            *
*   [OTHER]  +                        ---> VERB                            *
*                                                                          *
* VERB_DOT:                                                                *
*   (')     - ; CTokenOut(VERB)    ---> START                              *
*   [OTHER] token = token + ".";   ---> VERB                               *
***************************************************************************/


package tla2tex;
import java.util.Vector;

public class TokenizeComment
  { private static Vector vspec = new Vector(50, 50) ;
      /*********************************************************************
      * The vector that will eventually be turned into the array returned  *
      * by the Tokenize method.                                            *
      *********************************************************************/
      
    /***********************************************************************
    * The following private class variables are used in the                *
    * implementation of the Tokenize method.  They are made class          *
    * variables so they can be accessed in procedures used by Tokenize     *
    * (which are defined as private class methods).                        *
    ***********************************************************************/

    private static Vector linev = new Vector(40, 40) ;
          /*****************************************************************
          * Vector linev contains the tokens found so far on the current   *
          * line.                                                          *
          *****************************************************************/

    private static Vector argVec ;
      /*********************************************************************
      * The argument with which the Tokenize method is called, "exposed"   *
      * so that other methods, which are actually subprocedures of         *
      * Tokenize, can access it.  This hackery is needed because Java      *
      * apparently doesn't support static methods within a static method.  *
      * As someone once said, "I always program in the same language,      *
      * regardless of the compiler I happen to be using."                  *
      *********************************************************************/
      
    private static char nextChar ;
          /*****************************************************************
          * nextChar is the next input character to be processed.          *
          *****************************************************************/

    private static String token  = "" ;
          /*****************************************************************
          * token is the string containing the part of the current token   *
          * found so far.                                                  *
          *****************************************************************/

    private static boolean inDQuote = false ;
      /*********************************************************************
      * True iff have found the first of a presumed pair of '"'            *
      * characters.                                                        *
      *********************************************************************/
      
    private static boolean inSQuote = false ;
      /*********************************************************************
      * True iff have found the first of a presumed "`...'" expression,    *
      * which indicates that the expression is to be parsed as part of a   *
      * TLA spec.                                                          *
      *********************************************************************/
      
    private static int col ;
    private static int ncol = 0;
          /*****************************************************************
          * col is the column from which the first character of token      *
          * came.                                                          *
          *                                                                *
          * ncol is the column from which nextChar came.                   *
          *****************************************************************/
    private static int line = 0;
      /*********************************************************************
      * The line of comment (the element of the Vector argument of         *
      * Tokenize) currently being processed.                               *
      *********************************************************************/
      
    private static String curString = "";
      /*********************************************************************
      * This is the line of the comment currently being processed.  It     *
      * equals vec.elementAt(line), where vec is the argument to           *
      * Tokenize.                                                          *
      *********************************************************************/

    /***********************************************************************
    * Here are all the states for the tokenizing algorithm.                *
    ***********************************************************************/
      private static final int START            = 1 ;
      private static final int ID               = 2 ;
      private static final int NUM_OR_ID        = 3 ;
      private static final int BS               = 4 ;
      private static final int NUM_OR_BI        = 5 ;  
      private static final int NUM              = 6 ;
      private static final int BSBUILT_IN       = 7 ;  
      private static final int BUILT_IN         = 8 ;
      private static final int REPEAT_CHAR      = 9 ;
      private static final int STRING           = 10 ;
      private static final int ESC_STRING       = 11 ;
      private static final int LEFT_DQUOTE      = 12 ;
      private static final int RIGHT_DQUOTE     = 13 ;
      private static final int LEFT_SQUOTE      = 14 ;
      private static final int RIGHT_SQUOTE     = 15 ;
      private static final int TEX              = 16 ;
      private static final int TEX_CARET        = 17 ;
      private static final int THROW_AWAY       = 18 ;
      private static final int THROW_AWAY_TILDE = 19 ;
      private static final int VERB             = 20 ;
      private static final int VERB_DOT         = 21 ;
      private static final int DONE             = 22 ;
      
    private static int state = START ;
          /*****************************************************************
          * The state in the tokenizing algorithm.                         *
          *****************************************************************/
          
    /***********************************************************************
    * The following private methods are all procedures for use by the      *
    * Tokenize method.                                                     *
    ***********************************************************************/

    private static boolean isAllUnderscores()
      /*********************************************************************
      * True iff token is a string consisting only of "_" characters.      *
      *********************************************************************/
      { int i = 0 ;
        boolean result = true ;
        while ( result && (i < token.length()))
         { if (token.charAt(i) != '_') { result = false;} ;
           i=i+1;
         };
        return result;
      } ;

    private static void skipNextChar()
      /*********************************************************************
      * Sets nextChar to the next character in the input stream, and sets  *
      * ncol to its column.                                                *
      *********************************************************************/
      { ncol = ncol + 1;
        if (ncol < curString.length())
          {nextChar = curString.charAt(ncol);}
        else if (ncol == curString.length())
          {nextChar = '\n';}
        else
          { line = line + 1;
            if (line < argVec.size())
              { curString = (String) argVec.elementAt(line); 
                if (curString == null) {curString = "";}
              }
            else
             { curString = "\t"; } ;
            ncol = 0 ;
            if (curString.length() == 0)
             { nextChar = '\n';}
            else
             { nextChar = curString.charAt(0);} ;
          };
      } ;

    private static void addNextChar()
      /*********************************************************************
      * Appends nextChar to token, sets nextChar to the next character in  *
      * the input stream, and sets ncol to its column.                     *
      *********************************************************************/
      { token = token + nextChar ;
        skipNextChar() ;
      } ;

    private static void Backspace(int n) 
      /*********************************************************************
      * Decrements ncol by n.  (The result should be non-negative.)        *
      *********************************************************************/
      { ncol = ncol - n ;
        if (ncol < 0) 
          { Debug.ReportBug("TokenizeComment: Backspacing off end of line"); };
      }

    private static void gotoStart()
      /*********************************************************************
      * Set the state to START. Since this means that we are at or before  *
      * the beginning of the next token, we set col equal to ncol.         *
      *********************************************************************/
      { state = START ;
        col = ncol ;
      }

    private static void CTokenOut(int type)
      /*********************************************************************
      * Add the token to linev and reset token to the empty string.        *
      *********************************************************************/
      { if (   (! token.equals(""))
            || (type == CToken.STRING))
          /*****************************************************************
          * CTokenOut can be called with a null argument if the user       *
          * types "", or if she types ".'" at the beginning of a line or   *
          * immediately after "`.".  I'm not sure if there are other       *
          * cases as well.                                                 *
          *****************************************************************/
          { boolean tla = false ;
            boolean amb = false ;
            if ( (inSQuote) && (type != CToken.VERB))
             { tla = true ;
             }
            else
             { switch(type)
                { case CToken.BUILTIN :
                    if (FormatComments.isAmbiguous(token))
                      { /***************************************************
                        * We set the isAmbiguous flag for an ambiguous     *
                        * token only if that token actually appears in     *
                        * the spec.  This may be overly pessimistic,       *
                        * since it causes TLATeX to mess up the            *
                        * typesetting of a symbol fairly often.  Perhaps   *
                        * one should add an additional table for           *
                        * ambiguous tokens that should be considered       *
                        * ambiguous even if they don't appear in the spec  *
                        * because they're still more likely than not to    *
                        * be TLA symbols.  That table include "#".         *
                        ***************************************************/
                        if (TokenizeSpec.isUsedBuiltin(token))
                          {amb = true;};
                      }
                    else
                      { tla = true; }
                    break;
                  case CToken.NUMBER :
                    if (token.charAt(0) == '\\')
                      { tla = true ;}
                    else
                      { amb = true ;}
                    break;
                  case CToken.STRING :
                    tla = true;
                    break;
                  case CToken.IDENT :
                    if (FormatComments.IsWord(token))
                      { if (TokenizeSpec.isIdent(token))
                         { amb = true ;} ;
                      }
                    else
                      { if (TokenizeSpec.isIdent(token))
                              //   || (token.length() == 1)
                              // At first, it seemed like a good idea
                              // to consider any 1-character non-word 
                              // IDENT like "i" to be a symbol.  However, 
                              // a comment could include something like 
                              //   "There are two cases: (i)..."
                         { tla = true ;
                         }
                        else
                         { amb = true;
                         }
                      } ;
                    break;
                  case CToken.VERB :
                    if (token.indexOf("\\end{verbatim}") != -1)
                      /*****************************************************
                      * This is highly unlikely, but I discovered the      *
                      * problem when testing, so ...                       *
                      *****************************************************/
                     { Debug.ReportError(
                        "Sorry, but you can't put the string\n\n" +
                        "       \\end{verbatim}\n\n" +
                        "    between `. and .' ");
                     };
                    break;
                  case CToken.OTHER :
                  case CToken.REP_CHAR :
                  case CToken.LEFT_DQUOTE :
                  case CToken.RIGHT_DQUOTE :
                  case CToken.TEX :
                    break;
                  default :
                    Debug.ReportBug(
                     "TokenizeComment.CTokenOut called with illegal type"); 
                }
             }
            linev.addElement(new CToken(token, col, type, tla, amb)); 
          } ;
        token = "" ;
      } ;

    private static void startNewLine()
      /*********************************************************************
      * Append linev to vspec, reset linev, and set curString to the next  *
      * line of input.  This should be called whenever a \n character is   *
      * removed from the input stream.                                     *
      *********************************************************************/
      { vspec.addElement(linev)    ;
        linev = new Vector(30, 30) ;
        col = 0 ;
        ncol = 0 ;
      } ;

    private static CToken[][] vspecToArray() 
      /*********************************************************************
      * Turns vspec into an array, and re-initializes it.                  *
      *********************************************************************/
      { CToken[][] aspec = new CToken[vspec.size()][] ;
        int n = 0 ;                                                       
        while (n < vspec.size())                                          
          { aspec[n] =                                                     
               new CToken [ ((Vector) vspec.elementAt(n)) . size() ] ;     
            int m = 0 ;                                                   
            while (m < aspec[n].length)                                    
              {aspec[n][m] =                                               
                (CToken) ((Vector) vspec.elementAt(n)) . elementAt(m);     
               m = m+1;                                                   
              };                                                          
            n = n+1 ;                                                     
          };                                                              
        vspec = new Vector(50, 50) ;
        return aspec;
      } ;

    public static CToken[][] Tokenize(Vector vec)
      /*********************************************************************
      * Tokenize the comment represented by vec, which must be a vector    *
      * of strings.                                                        *
      *********************************************************************/
      { if ((vec == null) || (vec.size() == 0)) {return null ;} ;
          /*****************************************************************
          * A zero-length or null vector returns null.  Any caller who     *
          * provides such an argument had better be ready to deal with     *
          * the null result.                                               *
          *****************************************************************/

        argVec = vec;
          /*****************************************************************
          * Expose the argument to all the innocent methods in the         *
          * neighborhood.                                                  *
          *****************************************************************/

        line = 0 ;
        
        /*******************************************************************
        * Initialize curString and nextChar, col, and ncol.                *
        *******************************************************************/
        if (argVec.elementAt(line) == null)
          { curString = "" ;
          }
        else 
          { curString = (String) argVec.elementAt(line) ;
          } ;
        if (curString.equals(""))
          { nextChar  = '\n';}
        else
          { nextChar = curString.charAt(0) ;};
        col = 0 ;
        ncol = 0;

        char repChar = ' ';
          /*****************************************************************
          * The current repetition character.  (It is initialized only to  *
          * avoid a compiler warning.)                                     *
          *****************************************************************/

        state = START ;

        while (state != DONE)
          { // BEGIN while (state != DONE)
            /***************************************************************
            * Set linev to the vector of tokens in the current line.       *
            ***************************************************************/
            switch (state) 
              /*************************************************************
              * The following code is a direct translation of the          *
              * description given in the comments above, with only minor   *
              * optimizations that are local to a particular case clause.  *
              *************************************************************/
              { case START :
                  if (Misc.IsSpace(nextChar))
                    { skipNextChar() ;
                      gotoStart(); 
                    }
                  else if (Misc.IsLetter(nextChar))
                    { addNextChar();
                      state = ID;  
                    }
                  else if (Misc.IsDigit(nextChar))
                    { addNextChar();
                      state = NUM_OR_ID; 
                    }
                  else if (nextChar == '\n')
                    { skipNextChar() ;
                      startNewLine() ;
                      gotoStart(); 
                    }
                  else if (nextChar == '\\')
                    { addNextChar();
                      state = BS;    
                    }
                  else if (FormatComments.isRepeatChar(nextChar))
                    { repChar = nextChar;
                      addNextChar();
                      state = REPEAT_CHAR ;
                    }
                  else if (nextChar == '"')   // " )
                    { if (inDQuote)
                        { addNextChar();
                          state = RIGHT_DQUOTE;}
                      else
                        { skipNextChar();
                          state = STRING;};
                    }
                  else if (nextChar == '`')
                    { addNextChar();
                      state = LEFT_SQUOTE; 
                    }                              
                  else if (nextChar == '\'')
                    { if (inSQuote)
                        { skipNextChar();
                          inSQuote = false;
                          gotoStart();
                        }
                      else
                        { addNextChar();
                          state = RIGHT_SQUOTE; 
                        } ;
                    }                              
                  else if (BuiltInSymbols.IsBuiltInPrefix("" + nextChar))
                    { addNextChar();
                      state = BUILT_IN ;
                    }
                  else if (nextChar == '\t')
                    { state = DONE ;
                    }
                  else 
                    { addNextChar();
                      CTokenOut(CToken.OTHER);
                      gotoStart() ;
                    } ;
                  break;

                case ID :
                  if (   (token.length() == 3)
                      && (token.equals("WF_") || token.equals("SF_")))
                    { CTokenOut(CToken.BUILTIN) ;
                      gotoStart(); 
                    }
                  else if (Misc.IsLetter(nextChar) || Misc.IsDigit(nextChar))
                    { addNextChar();
                      // state = ID ;
                    }  
                  else if (BuiltInSymbols.IsBuiltInSymbol(token))
                            // don't want to handle PCal tokens specially
                    { CTokenOut(CToken.BUILTIN) ;
                      gotoStart();
                    }
                  else 
                    { if (isAllUnderscores())
                        { CTokenOut(CToken.REP_CHAR); }
                      else 
                        { CTokenOut(CToken.IDENT) ; };
                      gotoStart();
                    };
                  break;          

                case NUM_OR_ID :
                  if (Misc.IsDigit(nextChar))
                    { addNextChar();
                      state = NUM_OR_ID; 
                    }
                  else if (Misc.IsLetter(nextChar))
                    { addNextChar();
                      state = ID; 
                    }
                  else 
                    { CTokenOut(CToken.NUMBER) ;
                      gotoStart();
                    }
                  break;

                case BS :
                  if (    (nextChar == 'b') 
                       || (nextChar == 'B') 
                       || (nextChar == 'o') 
                       || (nextChar == 'O') 
                       || (nextChar == 'h') 
                       || (nextChar == 'H') )
                    { addNextChar();
                      state = NUM_OR_BI ;
                    }
                  else if (Misc.IsLetter(nextChar))
                    { state = BSBUILT_IN ; 
                    }
                  else 
                    { state = BUILT_IN ;
                    }
                  break;

                case NUM_OR_BI :
                  if (Misc.IsDigit(nextChar))
                    { state = NUM;
                    }
                  else 
                    { state = BSBUILT_IN;
                    };
                  break;

                case NUM :
                  if (Misc.IsDigit(nextChar))
                    { addNextChar();
                      state = NUM;
                    }
                  else if (Misc.IsLetter(nextChar) && (token.charAt(0) != '\\'))
                    { addNextChar();
                      state = ID;
                    }
                  else 
                    { CTokenOut(CToken.NUMBER) ;
                      gotoStart();
                    }
                  break;

                case BSBUILT_IN :
                  if (Misc.IsLetter(nextChar))
                    { addNextChar();
                      state = BSBUILT_IN;
                    }
                  else if (BuiltInSymbols.IsBuiltInSymbol(token))
                            // "\" built-in never a PCal symbol
                    { CTokenOut(CToken.BUILTIN) ;
                      gotoStart();
                    }
                  else 
                    { CTokenOut(CToken.OTHER) ;
                      gotoStart();
                    } ;
                   break;

                case BUILT_IN :
                  if (BuiltInSymbols.IsBuiltInPrefix(token + nextChar))
                    { addNextChar();
                      // state = BUILT_IN;
                    }
                  else 
                    { 
                     if (! BuiltInSymbols.IsBuiltInSymbol(token))
                         // don't want to handle PCal tokens specially
                      { 
                        while (! BuiltInSymbols.IsBuiltInSymbol(token))
                            // don't want to handle PCal tokens specially
                        { Backspace(1);
                          if (token.length() == 0)
                            { Debug.ReportBug(
                                 "Error tokenizing built-in symbol");
                            };
                          token = token.substring(0, token.length()-1);
                        } ;
                        nextChar = curString.charAt(ncol); 
                      } ;
                      CTokenOut(CToken.BUILTIN) ;
                      gotoStart();
                    }
                   break;

                case REPEAT_CHAR:
                  if (nextChar == repChar)
                    { addNextChar();
                      // state = REPEAT_CHAR ;
                    }
                  else if (token.length() >= 
                          FormatComments.getRepeatCharMin(repChar))
                    { CTokenOut(CToken.REP_CHAR);
                      state = START ;
                    }
                  else
                    { state = BUILT_IN ;
                    }
                  break;

                case STRING :
                  if (nextChar == '\\')
                    { addNextChar();
                      state = ESC_STRING ;
                    }
                  else if (BuiltInSymbols.IsStringChar(nextChar))
                    { addNextChar();
                      state = STRING ;
                    }
                  else if (  (nextChar == '"') // " )
                          && (   TokenizeSpec.isString(token)
                              || inSQuote ))
                    { 
                      skipNextChar();
                      CTokenOut(CToken.STRING) ;
                      gotoStart();
                    }
                  else
                    { state = LEFT_DQUOTE;
                    }
                   break;

                case ESC_STRING :
                  if (   (nextChar == '\"')
                      || (nextChar == '\\')
                      || (nextChar == 't')
                      || (nextChar == 'n')
                      || (nextChar == 'f')
                      || (nextChar == 'r') )
                    { addNextChar();
                      state = STRING ;
                    }
                  else
                    { state = LEFT_DQUOTE;
                    };
                  break;

                case LEFT_DQUOTE :
                  Backspace(token.length()+1);
                  token = "\"" ; 
                  CTokenOut(CToken.LEFT_DQUOTE);
                  inDQuote = true;
                  skipNextChar();
                  gotoStart();    
                  break;

                case RIGHT_DQUOTE :
                  CTokenOut(CToken.RIGHT_DQUOTE) ;
                  inDQuote = false ;
                  gotoStart();    
                  break;

                case LEFT_SQUOTE :
                  if (nextChar == '`')
                   { addNextChar();
                     CTokenOut(CToken.OTHER);
                     gotoStart();    
                   }
                  else if (nextChar == '^' )
                   { skipNextChar();
                     token = "  " ;
                     state = TEX ;
                   }
                  else if (nextChar == '~' )
                   { skipNextChar();
                     token = "  " ;
                     state = THROW_AWAY ;
                   }
                  else if (nextChar == '.' )
                   { skipNextChar();
                     token = "  " ;
                     state = VERB ;
                   }
                  else 
                   { token = "" ;
                     inSQuote = true;
                     // gotoStart();
                     col = ncol - 1;
                     state = START ;
                   }
                  break;

                case RIGHT_SQUOTE :
                  if (nextChar == '\'')
                    { addNextChar() ;
                      CTokenOut(CToken.OTHER) ;
                      gotoStart();
                    }
                  else
                    { state = BUILT_IN ;
                    }
                  break;

                case TEX :
                  if (nextChar == '^')
                   { skipNextChar();
                     state = TEX_CARET ;
                   }
                  else if (nextChar == '\n' )
                   { skipNextChar();
                     if (token == "")
                       { token = " "; }
                     CTokenOut(CToken.TEX);
                     startNewLine();
                     // state = TEX
                   }
                  else if (nextChar == '\t' )
                   { if (! Misc.isBlank(token))
                       {CTokenOut(CToken.TEX);} ;
                     token = "";
                     state = DONE ;
                   }
                  else 
                   { addNextChar();
                     // state = TEX ;
                   }
                  break;

                case TEX_CARET :
                  if (nextChar == '\'')
                   { skipNextChar();
                     if (! Misc.isBlank(token))
                       {CTokenOut(CToken.TEX);} ;
                     token = "";
                     gotoStart();
                   }
                   else 
                   { token = token + "^";
                     state = TEX ;
                   }
                  break;

                case THROW_AWAY :
                  if (nextChar == '~')
                   { skipNextChar();
                     state = THROW_AWAY_TILDE ;
                   }
                  else if (nextChar == '\n' )
                   { skipNextChar();
                     if (linev.size() != 0) 
                       /****************************************************
                       * Start new line iff there is some actual output    *
                       * on the line.                                      *
                       ****************************************************/
                       { startNewLine(); }
                     col = 0 ;
                     ncol = 0 ;
                     // state = THROW_AWAY
                   }
                  else if (nextChar == '\t' )
                   { state = DONE ;
                   }
                  else 
                   { addNextChar();
                     // state = THROW_AWAY ;
                   }
                  break;

                case THROW_AWAY_TILDE :
                  if (nextChar == '\'')
                   { skipNextChar();
                     token = "";
                     gotoStart();
                   }
                   else 
                   { skipNextChar();
                     state = THROW_AWAY ;
                   }
                  break;

                case VERB :
                  if (nextChar == '.')
                   { skipNextChar();
                     state = VERB_DOT;
                   }
                  else if (nextChar == '\n' )
                   { skipNextChar();
                     if (! Misc.isBlank(token))
                       {CTokenOut(CToken.VERB);} ;
                     token = "";
                     startNewLine();
                     // state = VERB ;
                   }
                  else if (nextChar == '\t' )
                   { if (! Misc.isBlank(token))
                       {CTokenOut(CToken.VERB);} ;
                     state = DONE ;
                   }
                  else 
                   { addNextChar();
                     // state = VERB ;
                   }
                  break;

                case VERB_DOT :
                  if (nextChar == '\'')
                   { skipNextChar();
                     CTokenOut(CToken.VERB) ;
                     gotoStart();
                   }
                   else 
                   { token = token + ".";
                     state = VERB ;
                   }
                  break;

                default :
                  Debug.ReportBug(
                    "Unexpected state in comment-parsing algorithm");
                  // break;

              } ;  // END switch (state)
         } ; // END while (state != DONE)

        /*******************************************************************
        * Return the contents of vspec, converted to an array.             *
        *******************************************************************/
        return vspecToArray();
      }

    public static CToken[][] TeXTokenize(Vector vec)
      /*********************************************************************
      * Tokenize the comment represented by vec, which must be a vector of *
      * strings, turning each line into a TeX token.                       *
      *********************************************************************/
      { if ((vec == null) || (vec.size() == 0)) {return null ;} ;
          /*****************************************************************
          * A zero-length or null vector returns null.  Any caller who     *
          * provides such an argument had better be ready to deal with     *
          * the null result.                                               *
          *****************************************************************/
        CToken[][] result = new CToken[vec.size()][];
        line = 0 ;
        while (line < vec.size())
         {String curString = "" ;
          if (vec.elementAt(line) != null)
           {curString = (String) vec.elementAt(line) ;
           } ;
          result[line] = new CToken[1];
          result[line][0] = new CToken(curString,0,CToken.TEX, false, false);
          line = line + 1;
         } ;
        return result ;
      }
 }

/* last modified on Wed  1 Nov 2006 at 11:29:38 PST by lamport */
/*      modified on Mon Dec 11 14:21:46 PT 2000 by unknown */
