/***************************************************************************
* CLASS Tokenize                                                           *
*                                                                          *
* The main methods of this class are                                       *
*                                                                          *
*    TLAExpr TokenizeExpr(PcalCharReader charReader)                       *
*                                                                          *
*       It returns a TLAExpr obtained by reading characters from           *
*       charReader.  It stops reading characters after it has read the     *
*       first token that follows the expression.  Upon return,             *
*                                                                          *
*           Tokenize.Delimiter                                             *
*              is the string that equals that following token.             *
*           Tokenize.DelimiterLine, Tokenize.DelimiterCol                  *
*              are the string's line and column numbers (first = 0)        *
*                                                                          *
*       It would be nicer if Tokenize simply left the reader               *
*       positioned before that following token.  However, this             *
*                                                                          *
*       Note: If there are line breaks between the position at which       *
*       this is called and the first token of the expression, then         *
*       these will produce null lines in the output.  I think that         *
*       will produce the proper translated output, but I'm not             *
*       positive.                                                          *
*                                                                          *
*    String  GetAlgorithmToken(PcalCharReader charReader)                  *
*       This returns the next token from charReader, ignoring TLA+         *
*       comments.  It is used for parsing the algorithm.                   *
*                                                                          *
* This class was written by modifying tlatex.TokenizeSpec.  The major      *
* changes are that it uses pcal.PcalBuiltInSymbols instead of              *
* tlatex.BuiltInSymbols (which defines ";" as an additional built-in       *
* token), CommentTokenOut was modified to throw away comments, and         *
* TokenOut was modified to end the parsing when the end of the expression  *
* is detected (and to detect some errors).                                 *
*                                                                          *
* In the +CAL grammar, an expression is ended by any of the following      *
* tokens (which follow the express, and are not part of it):               *
*                                                                          *
*   ;   variable   variables   begin   do   then   :=   ||                 *
*                                                                          *
* or by a ")" or a "," that does not match or occur inside an unmatched    *
* "(", "[", "{", or "<<" .                                                 *
*                                                                          *
* Because TokenizeExpr doesn't try to parse the expression but merely      *
* looks for a delimiter, an error in the algorithm text can cause it to    *
* gobble up a fair amount of the algorithm before it realizes that it's    *
* outside the expression.  For example, if one forgets the ";" and writes  *
*                                                                          *
*        x := x + 1                                                        *
*       if x > y + 17 then                                                 *
*                                                                          *
* then the parser keeps building the expression until it hits the "then",  *
* and reports the missing semicolon at that point.  Error reporting could  *
* be improved by being more aggressive at testing for the end of the       *
* expression.  For example, we could prohibit "if", "when", "while",       *
* "with", and "else" from appearing in an expression and test for them.    *
*                                                                          *
* Comment added by LL on 28 Feb 2006:                                      *
* Because the ParseAlgorithm.Uncomment method is now called before the     *
* algorithm is tokenized, the code here for handling comments is not       *
* needed.  However, an unmatched *) before the "end algorithm" could       *
* cause the tokenize methods in this class to encounter a comment.  An     *
* error should be reported if this happens.  This has not been done.       *
*                                                                          *
* ------------------------------------------------------------------       *
*                                                                          *
*    THE FOLLOWING IS THE DOCUMENTATION FROM tlatex.TokenizeSpec           *
*                                                                          *
* This class contains the Tokenize method that takes a CharReader for a    *
* TLA specification, or part of a specification, and tokenizes it.         *
* After tokenizing the spec, it provides the methods                       *
*                                                                          *
*    isIdent                                                               *
*    isUsedBuiltin                                                         *
*    isString                                                              *
*                                                                          *
* that tell whether a particular string appeared in the spec as an         *
* identifier, built-in operator, or TLA+ string.  These methods are used   *
* in TokenizeComment.Tokenize to try to determine if a comment token       *
* represents a specification symbol.                                       *
*                                                                          *
* The following comments are from tlatex.TokenizeSpec.  The description    *
* of TLA mode describes how tokens are parsed by the current module.       *
* However, in the current module, the parsing is normally stopped before   *
* the DONE state.                                                          *
*                                                                          *
* -----------------------------------------------------------------------  *
*                                                                          *
* The Tokenize method can be called in one of two modes:                   *
*                                                                          *
*   TLA mode    : It assumes that the input is any arbitrary portion       *
*                 of a TLA+ spec.                                          *
*   MODULE mode : It assumes that the input consists of arbitrary          *
*                 text, followed by a complete module, followed            *
*                 by arbitrary text.                                       *
*                                                                          *
* The result returned by Tokenize is an an array of arrays spec of Token   *
* objects, where spec[i][j] is token number j on line number i of the      *
* input, where the first line is numbered 0 and the first token of a line  *
* is numbered 0.                                                           *
*                                                                          *
* This is not quite a tokenizer for a parser for the following reasons:    *
*                                                                          *
*   -- Inner nested comments are thrown away.                              *
*                                                                          *
*   -- It keeps the "\" in escape sequences in strings.  For               *
*      example, when tokenizing the string "a\"b", it produces             *
*      the string with the four characters a \ " b instead                 *
*      of the three characters a " b, which is what a tool would           *
*      probably want.                                                      *
*                                                                          *
*   -- Expressions of the form "expr.WF_string" or "expr.SF_string"        *
*      are parsed as  "expr . WF_ string" instead of "expr . WF_string".   *
*      (This is a bug.)                                                    *
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
* The algorithm has a current state, which is initially START in TLA       *
* mode and PROLOG in MODULE mode.  When in a state S, the algorithm        *
* executes the <Action_Sequence> for the <State_Action> whose              *
* <State_Name> is S. It executes an <Action_Sequence> by going through     *
* its actions in order until it finds one whose <Precondition> is true.    *
* It then executes the <Step>s in that <Action>'s <Step_Sequence>, and     *
* then sets the current state to the <Action>'s <State_Name>.  However,    *
* the special <State_Name>s DONE and ERROR indicate that the algorithm     *
* is finished, either normally or with an error.                           *
*                                                                          *
* The algorithm uses the following variables:                              *
*                                                                          *
*    token :    The part of the token found so far.                        *
*                                                                          *
*    token1, token2, token3                                                *
*    col1,   col2,   col3   :                                              *
*               Temporary variables holding tokens and their starting      *
*               columns, used in processing the prolog.                    *
*                                                                          *
*    nextChar : The next character from the input stream                   *
*                                                                          *
*    cdepth :   The number of nested comments currently in.                *
*               (Equals 0 outside a comment.)                              *
*                                                                          *
*    mdepth :   The module nesting level.  (Determined by counting         *
*               "MODULE" keywords and "===="'s.                            *
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
*   TokenOut(type) and TokenOut(type, subtype) output  token               *
*     as a token of the indicated type and perhaps subtype,                *
*     and reset  token  to the empty string.                               *
*                                                                          *
* Here is the algorithm.                                                   *
*                                                                          *
* PROLOG:                                                                  *
*   ("-")     token1 := token; col1 := col ;                               *
*               token := "-" ; col := ncol; -     --> PROLOG_DASH          *
*   ("\n")    - ; TokenOut(PROLOG)                --> PROLOG               *
*   ("\t")                                        --> ERROR                *
*   [OTHER]   +                                   --> PROLOG               *
*                                                                          *
* PROLOG_DASH                                                              *
*   [("-") /\  Len(token) = 3]                                             *
*            +                        --> PROLOG_DASHES                    *
*   ("-")    +                        --> PROLOG_DASH                      *
*   [OTHER]  token := token1 + token; col := col1  --> PROLOG              *
*                                                                          *
* PROLOG_DASHES                                                            *
*   ("-")    +                              --> PROLOG_DASHES              *
*   [OTHER]  token2 := token ; token := "" ;                               *
*               col2 := col ; col = ncol    --> PROLOG_SPACES              *
*                                                                          *
* PROLOG_SPACES                                                            *
*   (" ")      +                                       --> PROLOG_SPACES   *
*   (Letter)   token3 := token ; col3 := ncol ;                            *
*                 token := ""                          --> PROLOG_ID       *
*   [OTHER]    token := token1 + token2 ; col := col1  --> PROLOG          *
*                                                                          *
* PROLOG_ID                                                                *
*   (Letter)  +                                            --> PROLOG_ID   *
*   [token = "MODULE"] token := token1; col := col1 ; TokenOut(PROLOG);    *
*                      token := token2; col := col2; TokenOut(DASHES);     *
*                      token := "MODULE"; col := col3;                     *
*                      TokenOut(BUILTIN);                                  *
*                      token := "" ;                                       *
*                      mdepth := 1                           --> START     *
*   [OTHER]   token := token1 + token2 + token3; col := col1 --> PROLOG    *
*                                                                          *
* START:                                                                   *
*   (Space_Char)          -  --> START                                     *
*   (Letter)              +  --> ID                                        *
*   (Digit)               +  --> NUM_OR_ID                                 *
*   ("\\")                +  --> BS                                        *
*   ("-")                 +  --> DASH1                                     *
*   ("=")                 +  --> EQ1                                       *
*   ("(")                 -  --> LEFT_PAREN                                *
*   ("\"")                -  --> STRING                                    *
*   ("\n")                -  --> START                                     *
*   (BuiltInPrefix)       +  --> BUILT_IN                                  *
*   [("\t") /\ TLA mode]     --> DONE                                      *
*   [OTHER]                  --> ERROR                                     *
*                                                                          *
* ID:                                                                      *
*   [token = "WF_" or "SF_"]  TokenOut(BUILTIN)     --> START              *
*   (Letter or Digit)         +                     --> ID                 *
*   [token = "MODULE"]        TokenOut(BUILTIN);                           *
*                             mdepth := mdepth + 1  --> START              *
*   [token \in BuiltIns]      TokenOut(BUILTIN)     --> START              *
*   [OTHER]                   TokenOut(IDENT)       --> START              *
*                                                                          *
* NUM_OR_ID:                                                               *
*   (Digit)   +                 --> NUM_OR_ID                              *
*   (Letter)  +                 --> ID                                     *
*   [OTHER]   TokenOut(NUMBER)  --> START                                  *
*                                                                          *
* BS:                                                                      *
*   ("b", "B", "o", "O", "h", or "H") +                --> NUM_OR_BI       *
*   (Letter)                                           --> BSBUILT_IN      *
*   ("*")                             - ; token := ""  --> LINE_COMMENT    *
*   [OTHER]                                            --> BUILT_IN        *
*                                                                          *
* NUM_OR_BI                                                                *
*   (Digit)   --> NUM                                                      *
*   [OTHER]   --> BSBUILT_IN                                               *
*                                                                          *
* NUM:                                                                     *
*   (Digit)  +                      --> NUM                                *
*   (Letter /\ token[1] != '\')   + --> ID                                 *
*   (Letter)                        --> ERROR                              *
*   [OTHER]  TokenOut(NUMBER)       --> START                              *
*                                                                          *
* BSBUILT_IN:                                                              *
*   (Letter)              +                  --> BSBUILT_IN                *
*   [token \in BuiltIns]  TokenOut(BUILTIN)  --> START                     *
*   [OTHER]                                  --> ERROR                     *
*                                                                          *
* BUILT_IN:                                                                *
*   [token+ \in BuiltInPrefix]  +                  --> BUILT_IN            *
*   [OTHER]   while (token \notin BuiltIn)                                 *
*               {move last char in token back                              *
*                to the CharReader};                                       *
*             TokenOut(BUILTIN)                    --> START               *
*                                                                          *
* DASH1:                                                                   *
*   ("-")   + --> DASH2                                                    *
*   [OTHER]   --> BUILT_IN                                                 *
*                                                                          *
* DASH2:                                                                   *
*   ("-")   + --> DASH3                                                    *
*   [OTHER]   --> BUILT_IN                                                 *
*                                                                          *
* DASH3:                                                                   *
*   ("-")   + --> DASHES                                                   *
*   [OTHER]   --> ERROR                                                    *
*                                                                          *
* DASHES:                                                                  *
*   ("-")   +                --> DASHES                                    *
*   [OTHER] TokenOut(DASHES) --> START                                     *
*                                                                          *
* EQ1:                                                                     *
*   ("=")   + --> EQ2                                                      *
*   [OTHER]   --> BUILT_IN                                                 *
*                                                                          *
* EQ2:                                                                     *
*   ("=")   + --> EQ3                                                      *
*   [OTHER]   --> BUILT_IN                                                 *
*                                                                          *
* EQ3:                                                                     *
*   ("=")   + --> EQS                                                      *
*   [OTHER]   --> ERROR                                                    *
*                                                                          *
* EQS:                                                                     *
*   ("=")   +                           --> EQS                            *
*   [TLA mode]  TokenOut(END_MODULE)    --> START                          *
*   [depth > 1] TokenOut(END_MODULE) ;                                     *
*               mdepth := mdepth - 1    --> START                          *
*   [depth = 1] TokenOut(END_MODULE) ;                                     *
*               mdepth := mdepth - 1    --> EPILOG                         *
*   [OTHER]                             --> ERROR                          *
*                                                                          *
* LEFT_PAREN:                                                              *
*   ("*")   - ; ; cdepth := 1   --> COMMENT                                *
*   [OTHER] token := "("        --> BUILT_IN                               *
*                                                                          *
* (**********************************************************)             *
* (* Note that we leave in the string the "\" of an escape  *)             *
* (* character like "\n".                                   *)             *
* (**********************************************************)             *
* STRING:                                                                  *
*   ("\\")             +                     --> ESC_STRING                *
*   ("\"")             - ; TokenOut(STRING)  --> START                     *
*   (LegalStringChar)  +                     --> STRING                    *
*   [OTHER]                                  --> ERROR                     *
*                                                                          *
* ESC_STRING:                                                              *
*   ("\"", "\\", "t", "n", "f", or "r")  + --> STRING                      *
*   [OTHER]                                --> ERROR                       *
*                                                                          *
* LINE_COMMENT:                                                            *
*   ("(")                 -                           --> LINE_COM_PAREN   *
*   [("*") /\ cdepth > 0]  -                          --> LINE_COM_STAR    *
*   ("\n" or "\t")        TokenOut(COMMENT, LINE)                          *
*                           ; cdepth := 0              --> START           *
*   [OTHER]               IF cdepth = 0 THEN + ELSE -  --> LINE_COMMENT    *
*                                                                          *
* LINE_COM_PAREN:                                                          *
*   ("*") - ; cdepth := cdepth + 1                   --> LINE_COMMENT      *
*   [OTHER]  IF cdepth = 0 THEN token := token + "("                       *
*                         ELSE                       --> LINE_COMMENT      *
*                                                                          *
* LINE_COM_STAR:                                                           *
*   (")")    - ; cdepth := cdepth - 1                 --> LINE_COMMENT     *
*   [OTHER]  IF cdepth = 0 THEN token := token + "*"                       *
*                          ELSE                       --> LINE_COMMENT     *
*                                                                          *
* COMMENT:                                                                 *
*   ("*")    -                                --> COMMENT_STAR             *
*   ("("}    -                                --> COMMENT_PAREN            *
*   ("\n")   TokenOut(COMMENT, BEGIN_OR) ; -  --> OR_COMMENT               *
*   ("\t")                                    --> ERROR                    *
*   [OTHER]  IF cdepth = 1 THEN + ELSE -      --> COMMENT                  *
*                                                                          *
*                                                                          *
* COMMENT_STAR:                                                            *
*   [(")") /\ cdepth = 1] - c; depth := cdepth - 1                         *
*                          ; TokenOut(COMMENT, NORMAL)  --> START          *
*   (")")                - ; cdepth := cdepth - 1       --> COMMENT        *
*   [OTHER]              IF cdepth = 1                                     *
*                          THEN token := token + "*"                       *
*                          ELSE                       --> COMMENT          *
*                                                                          *
* COMMENT_PAREN:                                                           *
*   ("*")    - ; cdepth := cdepth + 1                --> COMMENT           *
*   [OTHER]  IF cdepth = 1 THEN token := token + "("                       *
*                          ELSE                       --> COMMENT          *
*                                                                          *
* OR_COMMENT:                                                              *
*   ("*")    -                               --> OR_COMMENT_STAR           *
*   ("("}    -                               --> OR_COMMENT_PAREN          *
*   ("\n")   TokenOut(COMMENT, OVERRUN) ; -  --> OR_COMMENT                *
*   ("\t")                                   --> ERROR                     *
*   [OTHER]  IF cdepth = 1 THEN + ELSE -      --> OR_COMMENT               *
*                                                                          *
* OR_COMMENT_STAR:                                                         *
*   [(")") /\ cdepth = 1] - ; depth := depth - 1                           *
*                          ; TokenOut(COMMENT, END_OR)  --> START          *
*   (")")                - ; cdepth := cdepth - 1       --> OR_COMMENT     *
*   [OTHER]              IF cdepth = 1                                     *
*                          THEN token := token + "*"                       *
*                          ELSE                         --> OR_COMMENT     *
*                                                                          *
* OR_COMMENT_PAREN:                                                        *
*   ("*")    - ; cdepth := cdepth + 1                  --> OR_COMMENT      *
*   [OTHER]  IF cdepth = 1 THEN token := token + "("   --> OR_COMMENT      *
*                                                                          *
* EPILOG:                                                                  *
*   ("\n")  TokenOut(EPILOG) --> EPILOG                                    *
*   ("\t")  TokenOut(EPILOG) --> DONE                                      *
*   [OTHER] +                --> EPILOG                                    *
***************************************************************************/
package pcal;
import java.util.Vector;

import pcal.exception.TokenizerException;
import tla2tex.Misc;
import tla2tex.Symbol;
import tla2tex.Token;

public class Tokenize
  { private static final int MODULE = 1 ;
    private static final int TLA =    2 ;

    public static String Delimiter ;
    public static int DelimiterLine ;
    public static int DelimiterCol ;
      /*********************************************************************
      * Upon return, this equals the token following the expression.       *
      *********************************************************************/

      /*********************************************************************
      * The hash tables above are used only to remember the keys; there    *
      * is no value attached to them.  However, the Hashtable class        *
      * stores a non-null object with each key.  This is the object we     *
      * use.                                                               *
      *********************************************************************/

    /***********************************************************************
    * The following private class variables are used in the                *
    * implementation of the Tokenize method.  They are made class          *
    * variables so they can be accessed in procedures used by              *
    * TokenizedSpec (which are defined as private class methods).          *
    *                                                                      *
    * Note: This use of static fields makes the class totally thread       *
    * unsafe.                                                              *
    ***********************************************************************/
    private static Vector vspec = null ;
          /*****************************************************************
          * vspec is a vector of vectors in which the TokenizedSpec is     *
          * constructed.  At the end, it is turned into an array.          *
          *****************************************************************/

    private static Vector linev = new Vector(30, 30) ;
          /*****************************************************************
          * Vector linev contains the tokens found so far on the current   *
          * line.                                                          *
          *****************************************************************/

    private static char nextChar ;
          /*****************************************************************
          * nextChar is the next input character to be processed.          *
          *****************************************************************/

    /**
     * This is set to -1 when the last call to getNextChar returned a `\n',
     * and to 0 otherwise.  This is used by the TokenOut method, since if
     * a token is immediately followed by a `\n' character, then 
     * reader.getLineNumber will have been incremented before TokenOut
     * is called.
     */
    private static int getLineCorrection = 0 ;
    
    private static String token  = "" ;
    private static String token1 = "" ;
    private static String token2 = "" ;
    private static String token3 = "" ;
    private static int    col1   = 0 ;
    private static int    col2   = 0 ;
    private static int    col3   = 0 ;
          /*****************************************************************
          * token is the string containing the part of the token found so  *
          * far.                                                           *
          *                                                                *
          * token1, token2, and token3 are "temporary fields" holding a    *
          * previous value of token.                                       *
          *****************************************************************/

    private static int parenDepth = 0;
      /*********************************************************************
      * The current parenthesis nesting depth, where a parenthesis is      *
      * defined as a token of type BUILTIN whose corresponding Symbol      *
      * object has symbolType Symbol.LEFT_PAREN or Symbol.RIGHT_PAREN.     *
      *********************************************************************/

    private static boolean inQuantifier = false;
      /*********************************************************************
      * Set true if a `\A' or `\E' is found when parenDepth = 0, and set   *
      * false when a `:' is found with parenDepth = 0.  A comma does not   *
      * delimit the expression if encountered with inQuantifier = true.    *
      * This prevents the comma in an expression such as `\A i, j \in S :  *
      * P' from being interpreted as the end of the expression.  (A comma  *
      * found with parenDepth > 0 does not terminate the expression.)      *
      *********************************************************************/
      
    private static int cdepth = 0 ;
          /*****************************************************************
          * The nesting depth within "(*" ... "*)" comments.               *
          *****************************************************************/

    private static int mdepth = 0 ;
          /*****************************************************************
          * The module nesting depth.                                      *
          *****************************************************************/

    private static int col ;
    private static int ncol = 0;
          /*****************************************************************
          * col is the column from which the first character of token      *
          * came.                                                          *
          *                                                                *
          * ncol is the column from which nextChar came from.              *
          *****************************************************************/

/************* made public for DEBUGGING  ****************/
    public static PcalCharReader reader ;
      /*********************************************************************
      * This is the "exposed" version of the CharReader argument to the    *
      * TokenizedSpec constructor, exposed so it can be used by the        *
      * following procedures.                                              *
      *********************************************************************/

    /***********************************************************************
    * Here are all the states for the tokenizing algorithm.                *
    ***********************************************************************/
      private static final int PROLOG             = 1 ;
      private static final int PROLOG_DASH        = 2 ;
      private static final int PROLOG_DASHES      = 3 ;
      private static final int PROLOG_SPACES      = 4 ;
      private static final int PROLOG_ID          = 5 ;
      private static final int START              = 6 ;
      private static final int ID                 = 7 ;
      private static final int NUM_OR_ID          = 8 ;
      private static final int BS                 = 9 ;
      private static final int NUM                = 10 ;
      private static final int NUM_OR_BI          = 11 ;
      private static final int BSBUILT_IN         = 12 ;
      private static final int BUILT_IN           = 13 ;
      private static final int DASH1              = 14 ;
      private static final int DASH2              = 15 ;
      private static final int DASH3              = 16 ;
      private static final int DASHES             = 17 ;
      private static final int EQ1                = 18 ;
      private static final int EQ2                = 19 ;
      private static final int EQ3                = 20 ;
      private static final int EQS                = 21 ;
      private static final int LEFT_PAREN         = 22 ;
      private static final int STRING             = 23 ;
      private static final int ESC_STRING         = 24 ;
      private static final int LINE_COMMENT       = 25 ;
      private static final int LINE_COM_PAREN     = 26 ;
      private static final int LINE_COM_STAR      = 27 ;
      private static final int COMMENT            = 28 ;
      private static final int COMMENT_STAR       = 29 ;
      private static final int COMMENT_PAREN      = 30 ;
      private static final int OR_COMMENT         = 31 ;
      private static final int OR_COMMENT_PAREN   = 32 ;
      private static final int OR_COMMENT_STAR    = 33 ;
      private static final int EPILOG             = 34 ;
      private static final int DONE               = 35 ;
      
    private static int state = 0 ;
      /*********************************************************************
      * The state in the tokenizing algorithm.                             *
      *********************************************************************/

    private static boolean exprEnd = false;
      /*********************************************************************
      * Set true when at the end of the expression.                        *
      *********************************************************************/
      
    /***********************************************************************
    * The following private methods are all procedures for use by the      *
    * TokenizedSpec constructor.                                           *
    ***********************************************************************/


    private static void skipNextChar()
      /*********************************************************************
      * Sets nextChar to the next character in the input stream, and sets  *
      * ncol to its column.                                                *
      *********************************************************************/
      { ncol = reader.getColumnNumber();
        nextChar = reader.getNextChar();
        // See declaration of getLineCorrection for an explanation of:
        if (nextChar == '\n') {
            getLineCorrection = -1 ;
        } 
        else {
            getLineCorrection = 0 ;
        }
      } ;

    private static void addNextChar()
      /*********************************************************************
      * Appends nextChar to token, sets nextChar to the next character in  *
      * the input stream, and sets ncol to its column.                     *
      *********************************************************************/
      { token = token + nextChar ;
        skipNextChar() ;
      } ;

    private static void gotoStart()
      /*********************************************************************
      * Set the state to START. Since this means that we are at or before  *
      * the beginning of the next token, we set col equal to ncol.         *
      *********************************************************************/
      { state = START ;
        col = ncol ;
      }

    private static boolean parseExpression = true ;
      /*********************************************************************
      * The Tokenize method sets this value to its isExpr argument so the  *
      * TokenOut method can use it.  (Doing it the right way and making    *
      * it an argument of TokenOut would have required modifying all the   *
      * calls of TokenOut.)                                                *
      *********************************************************************/

    private static String prevToken = " " ;
      /*********************************************************************
      * Used by TokenOut to remember the previous token for figuring out   *
      * whether the current token is a record-field name rather than an    *
      * identifier.  This is needed to prevent a +cal reservered word      *
      * like "end" from screwing up the parsing when it is used as a       *
      * record-field name.  It is initialized in InnerTokenize and         *
      * set/reset by TokenOut.                                             
     * @throws TokenizerException *
      *********************************************************************/
      
    private static void TokenOut(int type) throws TokenizerException
      /*********************************************************************
      * If parseExpression is true, then add the token to linev and reset  *
      * token to the empty string unless it is the token following the     *
      * expression.  In that case, end the parsing and set Delimiter to    *
      * the token.  If parseExpression is false, then just set Delimiter   *
      * to the token and end the parsing.                                  *
      *********************************************************************/
      { if (parseExpression)
          { if (   (type == Token.BUILTIN)
                || (type == Token.NUMBER)
                || (type == Token.STRING)
                || (type == Token.IDENT) )
              { /***********************************************************
                * Check if this is a token that delimits the expression.   *
                ***********************************************************/
                if (   (type != Token.STRING)
                          /*************************************************
                          * Must not treat a string like ";" or "end" as   *
                          * delimiter.                                     *
                          *************************************************/
 
                    && (   (   IsDelimiter(token) 
                            && /********************************************
                               * Do not treat a reserved word like `end'   *
                               * as a delimiter if it may be a record      *
                               * field.                                    *
                               ********************************************/
                               ! (    (type == Token.IDENT)
                                   && (    prevToken.equals(".")
                                        || prevToken.equals("[")
                                        || prevToken.equals(","))))
                        || (   (   (    token.equals(",") 
                                     && ! inQuantifier)
                                || token.equals(")") 
                                || token.equals("}") 
                                   /****************************************
                                   * Test for "}" added 25 Mar 2006 to     *
                                   * permit c-syntax.                      *
                                   ****************************************/
                           )       
                            && (parenDepth == 0) ) )       )
                  { /*******************************************************
                    * The current token is the next one after the end of   *
                    * the expression.  Terminate the parsing by setting    *
                    * exprEnd to true and setting Delimiter to the         *
                    * current token.                                       *
                    *******************************************************/
                    if (parenDepth != 0)
                      {TokenizingError(
                         "Expression with an unmatched (, [, {, or << " +
                         "followed by");
                      } ;
                    if (inQuantifier)
                      {TokenizingError(
                         "Expression with \\A or \\E" +
                         " but no following `:` followed by");
                      } ;
                    exprEnd = true ;
                    Delimiter = token ;
                    DelimiterCol = col ;
                    DelimiterLine = reader.getLineNumber();
                    if (nextChar == '\n') 
                      {DelimiterLine = DelimiterLine - 1 ; } ;
    
                    /*******************************************************
                    * If current line is non-empty, add it to vspec.       *
                    *******************************************************/
                    if (linev.size() > 0)
                      { startNewLine() ; }
                  } 
                else
                 { /********************************************************
                   * Adjust parenDepth if necessary.                       *
                   ********************************************************/
                   if (type == Token.BUILTIN)
                     { Symbol sym = PcalBuiltInSymbols.GetBuiltInSymbol(token);
                       if (sym.symbolType == Symbol.LEFT_PAREN)
                         { parenDepth = parenDepth + 1; } ;
                       if (sym.symbolType == Symbol.RIGHT_PAREN)
                         { parenDepth = parenDepth - 1; 
                           if (parenDepth < 0)
                             { TokenizingError("Extra (unmatching)"); };
                         }
                     };
    
                   /********************************************************
                   * Set prevToken.  We set it to " " if the current       *
                   * token is a string so that, for example, the `end' in  *
                   * `"[" end' is recognized as the +cal reserved word     *
                   * and not considered to be a record field.              *
                   ********************************************************/
                   if (type == Token.STRING)
                     { prevToken = " " ; }
                   else 
                     { prevToken = token ; } ;

                   /********************************************************
                   * Set inQuantifier if necessary.                        *
                   ********************************************************/
                   if (    (   token.equals("\\A")
                            || token.equals("\\E"))
                        && (parenDepth == 0))
                     { inQuantifier = true ;} ;
                   if (    inQuantifier
                        && token.equals(":")
                        && (parenDepth == 0))
                     { inQuantifier = false ;} ;

                   /********************************************************
                   * Add the token to the expression.                      *
                   ********************************************************/
                   if (   (! token.equals(""))
                       || (type == Token.STRING))
                     /******************************************************
                     * I don't remember why I thought that TokenOut can    *
                     * be called with a null argument other than for the   *
                     * empty STRING. But, there are no other cases of      *
                     * non-comment tokens with empty strings, so the test  *
                     * seems harmless.                                     *
                     ******************************************************/
                	   /**
                	    * Line number argument added by LL for TLA-PCal mapping.
                	    * Experiment shows that it seems to do the right thing.
                	    * See the declaration of getLineCorrection for an explanation
                	    * of its use.
                	    */
                     { linev.addElement(new TLAToken(token, col, type, 
                             reader.getLineNumber() + getLineCorrection )); } ;   
                   /********************************************************
                   * Reset token.                                          *
                   ********************************************************/
                   token = "" ;
                  }
              }
            else
              { /***********************************************************
                * This is a token type that does not belong in an expression. *
                ***********************************************************/
                TokenizingError("Illegal token in an expression");
                   ;
              }
          }
        else
          { /***************************************************************
            * parseExpression = false                                      *
            ***************************************************************/
            exprEnd = true ;
            Delimiter = token ;
            DelimiterCol = col ;
            DelimiterLine = reader.getLineNumber();
            if (nextChar == '\n') {DelimiterLine = DelimiterLine - 1 ; } ;
            token = "" ;
          }
      }

    private static boolean IsDelimiter(String tok)
      /*********************************************************************
      * True iff tok is a token that does not belong to the expression,    *
      * and hence must be the next token after the expression.             *
      *********************************************************************/
      { return (   tok.equals(";")
                || tok.equals("do")
                || tok.equals("then")
                || tok.equals(":=")
                || tok.equals("begin")
                || tok.equals("variable")
                || tok.equals("variables")
                || tok.equals("||")

         // The following are added to improve error reporting
         // and to make possible the omission of some final ";"s. 
                || tok.equals("end")
                || tok.equals("else")
                || tok.equals("elsif")
                || tok.equals("if")
                || tok.equals("either")
                || tok.equals("or")
                || tok.equals("while")
                || tok.equals("with")
                || tok.equals("call")
                || tok.equals("return")
                || tok.equals("goto")
                || tok.equals("print")
                || tok.equals("assert")
                || tok.equals("skip")
                || tok.equals("procedure")
                || tok.equals("define")
                || tok.equals("process")
               ) ;
      }

    private static void CommentTokenOut()
      /*********************************************************************
      * Add the token to linev and reset token to the empty string.        *
      *                                                                    *
      * REFINED FOR pcal TO BE A NO-OP, AND TO TAKE NO ARGUMENT, SO        *
      * COMMENT TOKENS GET THROWN AWAY. THE ARGUMENT HAS BEEN REMOVED      *
      * FROM ALL CALLS TO CommentTokenOut.                                 *
      *********************************************************************/
      { token = "" ;
      }

    private static void startNewLine()
      /*********************************************************************
      * Append linev to vspec and reset linev.  This should be called      *
      * whenever a \n character is removed from the input stream.          *
      *********************************************************************/
      { vspec.addElement(linev)    ;
        linev = new Vector(30, 30) ;
        col = 0 ;
      }

    private static void TokenizingError(String msg) throws TokenizerException 
      { throw new TokenizerException(
           msg + " `" + token + "' found at\n" + 
          "    line " + (reader.getLineNumber() + 1) + ", column " + 
               (col + 1));
      }


    public static TLAExpr TokenizeExpr(PcalCharReader charReader) throws TokenizerException
      { TLAExpr exp = InnerTokenize(charReader, true) ;
        return exp ; }

    public static String GetAlgorithmToken(PcalCharReader charReader) throws TokenizerException
      { TLAExpr exp = InnerTokenize(charReader, false) ;
        return Delimiter ; }

    public static TLAExpr InnerTokenize(PcalCharReader charReader, 
                                    boolean isExpr) throws TokenizerException 
      /*********************************************************************
      * Tokenize the input from the CharReader.  If isExpr is true, then   *
      * an expression from the input is tokenized and Delimiter is set to  *
      * the following token.  If isExpr is false, then a single            *
      * non-comment token is tokenized, Delimiter is set to that token,    *
      * and a null TLAExpr is returned.                                    *
      *********************************************************************/
      { int mode = TLA ;
        /*******************************************************************
        * Modified by LL on 1 Feb 2006 to initialize ncol and col.  This   *
        * is needed because the use of PcalCharReader.peek() between       *
        * calls to the methods in the Tokenize class can cause the         *
        * current values to be off, leading to wrong column numbers for    *
        * tokens, which can cause misalignment.                            *
        *******************************************************************/
        ncol = charReader.getColumnNumber() ;
        col  = ncol ;
        parseExpression = isExpr ;
        prevToken = " ";
        vspec = new Vector(4) ;
          // Changed by LL on 13 Dec 2011 from new Vector(1000, 1000) ;
          // I don't know why such a large vector was being used
        reader = charReader ;
           /****************************************************************
           * This "exports" the charReader for use by the class's other    *
           * (private) methods.                                            *
           ****************************************************************/

        linev = new Vector() ;
          /*****************************************************************
          * I don't know where linev is initialized, but adding this       *
          * initialization doesn't seem to make any difference.            *
          *****************************************************************/

        token = "" ;
        nextChar = reader.getNextChar();
          /*****************************************************************
          * Initialize nextChar.                                           *
          *****************************************************************/
        // See declaration of getLineCorrection for an explanation of:
        if (nextChar == '\n') {
            getLineCorrection = -1 ;
        } 
        else {
            getLineCorrection = 0 ;
        }

        parenDepth = 0 ;
        inQuantifier = false ;

        switch (mode)
          { case MODULE : state = PROLOG ; break ;
            case TLA    : state = START  ; break ;
            default     : PcalDebug.ReportBug(
                           "TokenizeSpec.Tokenize called with illegal mode") ;
          } ;

        exprEnd = false ;

        while ((state != DONE) &&  ! exprEnd)
          { /***************************************************************
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
                  else if (nextChar == '\\')
                    { addNextChar();
                      state = BS;    
                    }
                  else if (nextChar == '-')
                    { addNextChar();
                      state = DASH1; 
                    }
                  else if (nextChar == '=')
                    { addNextChar();
                      state = EQ1; 
                    }                              
                  else if (nextChar == '(')   // )
                    { skipNextChar() ;
                      state = LEFT_PAREN; 
                    }
                  else if (nextChar == '"')   // " )
                    { skipNextChar();
                      state = STRING;  }
                  else if (nextChar == '\n')
                    { skipNextChar() ;
                      startNewLine() ;
                      gotoStart(); 
                    }
                  else if (PcalBuiltInSymbols.IsBuiltInPrefix("" + nextChar))
                    { addNextChar();
                      state = BUILT_IN ;
                    }
                  else if (nextChar == '\t')
                    { if (mode == MODULE) 
                        { throw new TokenizerException(
                            "Input ended before end of module");
                        } ;
                      state = DONE ;
                    }
                  else 
                    { addNextChar();
                      TokenizingError("Illegal lexeme");
                    } ;
                  break;

                case ID :
                  if (   (token.length() == 3)
                      && (token.equals("WF_") || token.equals("SF_")))
                    { TokenOut(Token.BUILTIN) ;
                      gotoStart(); 
                    }
                  else if (Misc.IsLetter(nextChar) || Misc.IsDigit(nextChar))
                    { addNextChar();
                      // state = ID ;
                    }  
                  else if (PcalBuiltInSymbols.IsBuiltInSymbol(token))
                    { if (token.equals("MODULE")) 
                        { mdepth = mdepth + 1; 
                        }
                      TokenOut(Token.BUILTIN) ;
                      gotoStart();
                    }
                  else 
                    { TokenOut(Token.IDENT) ;
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
                    { TokenOut(Token.NUMBER) ;
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
                  else if (nextChar == '*')
                    { skipNextChar();
                      token = "" ;
                      state = LINE_COMMENT ;
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
                  else if (Misc.IsLetter(nextChar))
                    { addNextChar();
                      if (token.charAt(0) == '\\')
                       { TokenizingError("Illegal lexeme");
                       }
                      else
                       { state = ID;
                       };
                    }
                  else 
                    { TokenOut(Token.NUMBER) ;
                      gotoStart();
                    }
                  break;

                case BSBUILT_IN :
                  if (Misc.IsLetter(nextChar) && (nextChar != '_'))
                        // added test for /= '_' on 21 Feb 2004
                        // to correct bug
                    { addNextChar();
                      state = BSBUILT_IN;
                    }
                  else if (PcalBuiltInSymbols.IsBuiltInSymbol(token))
                    { TokenOut(Token.BUILTIN) ;
                      gotoStart();
                    }
                  else 
                    { TokenizingError("Illegal lexeme ");
                    } ;
                   break;

                case BUILT_IN :
                  if (PcalBuiltInSymbols.IsBuiltInPrefix(token + nextChar))
                    { addNextChar();
                      // state = BUILT_IN;
                    }
                  else 
                    { 
                     if (! PcalBuiltInSymbols.IsBuiltInSymbol(token))
                      { 
                        reader.backspace();
                        while (! PcalBuiltInSymbols.IsBuiltInSymbol(token))
                        { reader.backspace();
                          if (token.length() == 0)
                            { TokenizingError("Illegal lexeme");
                            };
                          token = token.substring(0, token.length()-1);
                        } ;
                        // On 11 Jan 2011, LL changed
                        //
                        //     nextChar = reader.getNextChar();
                        //
                        // to the following so ncol gets set to the correct value in 
                        // case multiple reader.backspace calls occurred.  This fixed
                        // a bug that caused parsing "(\E x...)" to put the "\E" token
                        // one column too far to the right, causing it to be output
                        // as "( \Ex...)".
                        skipNextChar();
                       
                      } ;
                      TokenOut(Token.BUILTIN) ;
                      gotoStart();
                    }
                   break;

                case DASH1 :
                  if (nextChar == '-')
                    { addNextChar();
                      state = DASH2 ;
                    }
                  else 
                    { state = BUILT_IN ;
                    }
                  break;

                case DASH2 :
                  if (nextChar == '-')
                    { addNextChar();
                      state = DASH3 ;
                    }
                  else 
                    { state = BUILT_IN ;
                    }
                  break;

                case DASH3 :
                  if (nextChar == '-')
                    { addNextChar();
                      state = DASHES ;
                    }
                  else 
                    { TokenizingError("Illegal lexeme");
                    }
                  break;

                case DASHES :
                  if (nextChar == '-')
                    { addNextChar();
                      state = DASHES ;
                    }
                  else 
                    { TokenOut(Token.DASHES) ;
                      gotoStart();
                    }
                  break;

                case EQ1 :
                  if (nextChar == '=')
                    { addNextChar();
                      state = EQ2 ;
                    }
                  else 
                    { state = BUILT_IN ;
                    }
                  break;

                case EQ2 :
                  if (nextChar == '=')
                    { addNextChar();
                      state = EQ3 ;
                    }
                  else 
                    { state = BUILT_IN ;
                    }
                  break;

                case EQ3 :
                  if (nextChar == '=')
                    { addNextChar();
                      state = EQS ;
                    }
                  else 
                    { TokenizingError("Illegal lexeme");
                    }
                  break;

                case EQS :
                  if (nextChar == '=')
                    { addNextChar();
                      state = EQS ;
                    }
                  else 
                    { mdepth = mdepth - 1 ;
                      TokenOut(Token.END_MODULE) ;
                      if ((mdepth > 0) || (mode == TLA))
                        { gotoStart();
                        }
                      else if (mdepth == 0)
                        { state = EPILOG ;
                        }
                      else 
                        { throw new TokenizerException(
                           "Extra end-of-module lexeme on line "
                           + (reader.getLineNumber() + 1));
                        }
                    }
                  break;

                case LEFT_PAREN :
                  if (nextChar == '*')
                    { skipNextChar();
                      cdepth = 1;
                      state = COMMENT ;
                    }
                  else
                    { token = "(" ;
                      state = BUILT_IN ;
                    }

                  break;

                case STRING :
                  if (nextChar == '\\')
                    { addNextChar();
                      state = ESC_STRING ;
                    }
                  else if (nextChar == '"') // " )
                    { skipNextChar();
                      TokenOut(Token.STRING) ;
                      gotoStart();
                    }
                  else if (PcalBuiltInSymbols.IsStringChar(nextChar))
                    { addNextChar();
                      state = STRING ;
                    }
                  else
                    { addNextChar();
                      TokenizingError("Illegal character in string");
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
                    { addNextChar();
                      TokenizingError(
                          "Illegal character following \\ in string");
                    }
                  break;

                case LINE_COMMENT :
                  if (nextChar == '(')   // )
                    { skipNextChar();
                      state = LINE_COM_PAREN;
                    }
                  else if ((nextChar == '*') && (cdepth > 0))
                    { skipNextChar();
                      state = LINE_COM_STAR;
                    }
                  else if ((nextChar == '\n') || (nextChar == '\t'))
                    { CommentTokenOut() ;
                      cdepth = 0 ;
                      gotoStart();
                    }
                  else
                    { if (cdepth == 0) {addNextChar();}
                        else {skipNextChar();} ;
                      state = LINE_COMMENT;
                    }
                  break;

                case LINE_COM_PAREN :
                  if (nextChar == '*')
                    { skipNextChar();
                      cdepth = cdepth + 1;
                      state = LINE_COMMENT;
                    }
                  else
                    { if (cdepth == 0) {token = token + "(";} ;
                      state = LINE_COMMENT;
                    }
                  break;

                case LINE_COM_STAR :   // (     
                  if (nextChar == ')')  
                    { skipNextChar();
                      cdepth = cdepth - 1;
                      PcalDebug.Assert(cdepth >= 0,
                                   "case LINE_COM_STAR");
                      state = LINE_COMMENT;
                    }
                  else
                    { if (cdepth == 0) {token = token + "*";} ;
                      state = LINE_COMMENT;
                    }
                  break;

                case COMMENT :
                  if (nextChar == '*')
                    { skipNextChar();
                      state = COMMENT_STAR;
                    }
                  else if (nextChar == '(')  // )
                    { skipNextChar();
                      state = COMMENT_PAREN;
                    }
                  else if (nextChar == '\n')
                    { CommentTokenOut() ;
                      skipNextChar();
                      startNewLine();
                      state = OR_COMMENT;
                    }
                  else if (nextChar == '\t')
                    { throw new TokenizerException(
                         "Input ended in the middle of a comment");
                    }
                  else
                    { if (cdepth == 1) {addNextChar();}
                        else {skipNextChar();};
                      // state = COMMENT ;
                    }

                  break;

                case COMMENT_STAR :       // (
                  if (nextChar == ')')
                    { skipNextChar();
                      cdepth = cdepth - 1;
                      if (cdepth == 0)
                        { CommentTokenOut();
                          gotoStart();
                        }
                      else
                        { state = COMMENT;
                        }
                    }
                  else
                    { if (cdepth == 1) {token = token + "*";};
                      state = COMMENT;
                    }
                  break;

                case COMMENT_PAREN :
                  if (nextChar == '*')
                    { skipNextChar();
                      cdepth = cdepth + 1;
                      state = COMMENT;
                    }
                  else
                    { if (cdepth == 1) {token = token + "(";};
                      state = COMMENT;
                    }
                  break;

                case OR_COMMENT :
                  if (nextChar == '*')
                    { skipNextChar();
                      state = OR_COMMENT_STAR;
                    }
                  else if (nextChar == '(')  // )
                    { skipNextChar();
                      state = OR_COMMENT_PAREN;
                    }
                  else if (nextChar == '\n')
                    { CommentTokenOut() ;
                      skipNextChar();
                      startNewLine();
                      state = OR_COMMENT;
                    }
                  else if (nextChar == '\t')
                    { throw new TokenizerException(
                         "Input ended in the middle of a multi-line comment");
                    }
                  else
                    { if (cdepth == 1) {addNextChar();}
                        else {skipNextChar();};
                      // state = OR_COMMENT ;
                    }
                  break;

                case OR_COMMENT_STAR :    // (
                  if (nextChar == ')')
                    { skipNextChar();
                      cdepth = cdepth - 1;
                      PcalDebug.Assert(cdepth >= 0);
                      if (cdepth == 0)
                        { CommentTokenOut();
                          gotoStart();
                        }
                      else
                        { state = OR_COMMENT;
                        }
                    }
                  else
                    { if (cdepth == 1) {token = token + "*";};
                      state = OR_COMMENT;
                    }
                  break;

                case OR_COMMENT_PAREN :
                  if (nextChar == '*')
                    { skipNextChar();
                      cdepth = cdepth + 1;
                      state = OR_COMMENT;
                    }
                  else
                    { if (cdepth == 1) {token = token + "(";};
                      state = OR_COMMENT;
                    }
                  break;

                case PROLOG :
                  if (nextChar == '-')
                    { token1 = token ;
                      col1   = col ;
                      col    = ncol ;
                      token  = "-" ;
                      skipNextChar();
                      state = PROLOG_DASH ;
                    } 
                  else if (nextChar == '\n')
                    { TokenOut(Token.PROLOG) ;
                      skipNextChar();
                      startNewLine();
                      // state = PROLOG ;
                    }
                  else if (nextChar == '\t')
                    { throw new TokenizerException(
                         "Input ended before beginning of module");
                    }
                  else
                    { addNextChar();
                      // state = PROLOG ;
                    }
                break;

                case PROLOG_DASH :
                  PcalDebug.Assert(token.length() <= 3) ;
                  if (nextChar ==   '-')
                    { addNextChar();
                      if (token.length() == 4)
                        { state = PROLOG_DASHES;
                        }
                      else
                        { // state = PROLOG_DASH
                        } ;
                    }
                  else 
                    { token = token1 + token ;
                      col   = col1 ;
                      state = PROLOG ;
                    }
                  break;

                case PROLOG_DASHES :
                  if (nextChar == '-')
                    { addNextChar();
                      // state = PROLOG_DASHES ;
                    }
                  else 
                    { token2 = token ;
                      col2   = col ;
                      token  = "" ;
                      col    = ncol;
                      state  = PROLOG_SPACES ;
                    }
                  break;

                case PROLOG_SPACES :
                  if (nextChar == ' ')
                    { addNextChar();
                      // state = PROLOG_SPACES;
                    }
                  else if (Misc.IsLetter(nextChar))  
                    { token3 = token;
                      col3   = ncol ;
                      token  = "" ;
                      state  = PROLOG_ID ;
                    }
                  else 
                    { token  = token1 + token2 ;
                      col    = col1 ;
                      state  = PROLOG ;
                    }
                  break;
	      
                case PROLOG_ID :
                  if (Misc.IsLetter(nextChar))  
                    { addNextChar();
                      // state = PROLOG_ID ;
                    }
                  else if (token.equals("MODULE"))  
                    { token = token1 ;
                      col = col1;
                      TokenOut(Token.PROLOG) ;
                      token = token2 ;
                      col = col2;
                      TokenOut(Token.DASHES) ;
                      token = "MODULE" ;
                      col = col3;
                      TokenOut(Token.BUILTIN) ;
                      token  = "" ;
                      mdepth = 1 ;
                      gotoStart();
                    }
                  else 
                    { token = token1 + token2 + token3 ;
                      col = col1;
                      state  = PROLOG ;
                    }
                  break;

                case EPILOG :
                  if (nextChar == '\n')
                    { TokenOut(Token.EPILOG) ;
                      skipNextChar();
                      startNewLine();
                      // state = EPILOG ;
                    }
                  else if (nextChar == '\t')
                    { TokenOut(Token.EPILOG) ;
                      state = DONE ;
                    }
                  else
                    { addNextChar();
                      // state = EPILOG ;
                    }
                break;

                default :
                  PcalDebug.ReportBug(
                    "Illegal state in TokenizeSpec.Tokenize");
                  // break;

              } ;  // ends switch
         } ; // ends while

        /*******************************************************************
        * Need to backspace one character because it has already read one  *
        * character further--unless nextChar = \n (and the reader is       *
        * therefore at the beginning of the next line).                    *
        *******************************************************************/
        if (nextChar != '\n')
          { reader.backspace(); } ;

        /*******************************************************************
        * Returns a normalized TLAExpr made from vspec.                    *
        *******************************************************************/
        TLAExpr rval = new TLAExpr(vspec) ;
        rval.normalize() ;
        return rval;
      }
  }


/* last modified on Sat 25 Mar 2006 at  8:18:49 PST by lamport */

/*
In the +cal grammar, an <Expr> can be followed by the following:
Modify the TokenOut method to detect the end of the expression,
which is either one of the following tokens

  ;
  variable variables begin  [when it follows "procedure <Name> =|\in "]
  begin
  do
  then
  :=
  ||

or else an unmatched ")" or a "," that does not occur inside
parentheses of some form.  (It's "call( <Expr> [, <Expr> ]^* )"
that requires this hack.)

Note: In <LHS>, we regard everything between the <Variable>
      and the := to be an <Expr>.


      
*/

