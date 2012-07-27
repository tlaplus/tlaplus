// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS TokenizeSpec                                                       *
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
* The Tokenize method can be called in one of two modes:                   *
*                                                                          *
*   TLA mode     : It assumes that the input is any arbitrary portion      *
*                  of a TLA+ spec. (Called by tlatex.TeX for a tla         *
*                  environment.)                                           *
*   MODULE mode  : It assumes that the input consists of arbitrary         *
*                  text, followed by a complete module, followed           *
*                  by arbitrary text.                                      *
*   PLUSCAL mode : It assumes that the input consists of all or part of    *
*                  a C-Syntax PlusCal algorithm.  (Called by tlatex.TeX    *
*                  for a pcal environment.)                                *
*                                                                          *
*   P_PLUSCAL mode : It assumes that the input consists of all or part of  *
*                    a C-Syntax PlusCal algorithm.  (Called by tlatex.TeX  *
*                    for a ppcal environment.)                             *
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
*    pseudoCom : A boolean that equals true iff the next comment token to  * MODIFIED
*                be output either does not end with "*)" (because it was   * MODIFIED
*                terminated by the start of a PlusCal algorithm) or does   * MODIFIED
*                not begin with a "(*" (because it immediately followed    * MODIFIED
*                the end of a PlusCal algorithm).                          * MODIFIED
*                                                                          *
*    ORCom : A boolean set when looking for the start of a PlusCal         * MODIFIED
*            algorithm when processing a comment.  It equals true if       * MODIFIED
*            processing an OR (OverRun) comment, and false if processing a * MODIFIED
*            normal comment.                                               * MODIFIED
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
*   [OTHER /\ inPcal /\ canBeLabel]                                        * MODIFIED
*                             token1 := token       --> ID_OR_PCAL_LABEL   * MODIFIED
*   [OTHER]                   TokenOut(IDENT)       --> START              * MODIFIED
*                                                                          *
* ID_OR_PCAL_LABEL:                                                        * MODIFIED
*   \* Note: token1 contains id                                            * MODIFIED
*   (Space_Char)    +                     --> ID_OR_PCAL_LABEL             * MODIFIED
*   (":")           +   token1 := token   --> PCAL_LABEL                   * MODIFIED
*                                                                          *
* PCAL_LABEL:                                                              * MODIFIED
*   (Space_Char)    +                        --> PCAL_LABEL                * MODIFIED
*   ("+" or "-")    +  TokenOut(PCAL_LABEL)  --> START                     * MODIFIED
*   [OTHER]         token := token1;                                       * MODIFIED
*                   TokenOut(PCAL_LABEL)     --> START                     * MODIFIED
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
*             saved := CanPrecedeLabel(token)                              * MODIFIED
*             TokenOut(BUILTIN)                                            * MODIFIED
*             canBeLabel := saved                  --> START               * MODIFIED
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
*   [("-") /\ cdepth = 1 /\  mode = MODULE /\ ~hasPcal]                    * MODIFIED
*                        token1 := token;  col1 := col                     * MODIFIED
*                        token := "";  col := ncol (?)                     * MODIFIED
*                        ORCom := false ;                                  * MODIFIED
*                        +                              --> C_DASH         * MODIFIED
*   [OTHER]  IF cdepth = 1 THEN + ELSE -      --> COMMENT                  *
*                                                                          *
*                                                                          *
* COMMENT_STAR:                                                            *
*   [(")") /\ cdepth = 1] - c; depth := cdepth - 1                         *
*                            inPcal := false                               * MODIFIED      
*                          ; TokenOut(COMMENT, NORMAL)  --> START          *
*   (")")                - ; cdepth := cdepth - 1       --> COMMENT        *
*   [OTHER]              IF cdepth = 1                                     *
*                          THEN token := token + "*"                       *
*                          ELSE                       --> COMMENT          *
*                                                                          *
* C_DASH:                                                                  * MODIFIED
*   ("-")      +                            --> C_DASH_DASH                * MODIFIED
*   [OTHER]    token := token1 \o token; 
*              col := col1               +  --> COMMENT                    * MODIFIED
*                                                                          * MODIFIED
* C_DASH_DASH:                                                             * 
*   (Letter)    + --> C_DASH_DASH
*   [OTHER]   IF token \in {"--fair", "--algorithm"}
*               THEN 
*               ELSE token := token1 \o token        --> COMMENT
*                                                                          *
* COMMENT_PAREN:                                                           *
*   ("*")    - ; cdepth := cdepth + 1                --> COMMENT           *
*   [OTHER]  IF cdepth = 1 THEN token := token + "("                       *
*                          ELSE                       --> COMMENT          *
*                                                                          *
* OR_COMMENT:    (OR = OverRun)                                            *
*   ("*")    -                               --> OR_COMMENT_STAR           *
*   ("("}    -                               --> OR_COMMENT_PAREN          *
*   ("\n")   TokenOut(COMMENT, OVERRUN) ; -  --> OR_COMMENT                *
*   [("-") /\ cdepth = 1 /\  mode = MODULE /\ ~hasPcal]                    * MODIFIED
*                        token1 := token;  col1 := col                     * MODIFIED
*                        token := "";  col := ncol (?)                     * MODIFIED
*                        ORCom := true ;                                   * MODIFIED
*                        +                              --> C_DASH         * MODIFIED
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
package tla2tex;
import java.util.Hashtable;
import java.util.Vector;

public class TokenizeSpec
  { private static Hashtable identHashTable  = new Hashtable(1000);
      /*********************************************************************
      * A hash table containing all the IDENT and STRING tokens found in   *
      * the spec.  It is used for formatting comments.                     *
      *                                                                    *
      * Note: In comments, people seem to refer to the spec's strings      *
      * without the ""s, using them as if they were identifiers.  So, we   *
      * add them to the identHashTable just like identifiers.              *
      *********************************************************************/

    public static boolean isIdent(String str) 
      /*********************************************************************
      * Returns true iff str is an IDENT token in the spec.                *
      *********************************************************************/
      { return null !=  identHashTable.get(str);
      }

    private static Hashtable usedBuiltinHashTable  = new Hashtable(1000);
      /*********************************************************************
      * A hash table containing all the BUILTIN tokens found in the spec.  *
      * It is used for formatting comments.                                *
      *********************************************************************/

    public static boolean isUsedBuiltin(String str) 
      /*********************************************************************
      * Returns true iff str is a BUILTIN token in the spec.               *
      *********************************************************************/
      { return null !=  usedBuiltinHashTable.get(str);
      }

    private static Hashtable stringHashTable  = new Hashtable(100);
      /*********************************************************************
      * A hash table containing all the STRING tokens found in the spec.   *
      * It is used for formatting comments.                                *
      *********************************************************************/
    public static boolean isString(String str) 
      /*********************************************************************
      * Returns true iff str is a STRING token in the spec.                *
      *********************************************************************/
      { return null !=  stringHashTable.get(str);
      }

    private static String nullString = "" ;
      /*********************************************************************
      * The hash tables above are used only to remember the keys; there    *
      * is no value attached to them.  However, the Hashtable class        *
      * stores a non-null object with each key.  This is the object we     *
      * use.                                                               *
      *********************************************************************/
      
    // The modes
    public static final int MODULE    = 1 ;
    public static final int TLA       = 2 ;
    public static final int PLUSCAL   = 3 ;
    public static final int P_PLUSCAL = 4 ;

    /*
     * The following public fields are set by the Tokenize method to 
     * indicate the presence, location, and type of any PlusCal code
     * found in the input. 
     * 
     *   hasPcal : True iff in PLUSCAL mode or a PlucCal algorithm has
     *             been discovered.
     *             
     *   isCSyntax : If hasPCal is true, then this is true iff we are
     *               in PLUSCAL mode or we are in MODULE mode and 
     *               the --algorithm or --fair token has been found and it 
     *               begins a C-Syntax PlusCal algorithm.
     *               
     *   pcalStart
     *   pcalEnd   : The Positions of the first and last token of PlusCal
     *               code.  They will be set to null if there is no PlusCal code.
     */
    public static boolean hasPcal ;
    public static boolean isCSyntax ;
    public static Position pcalStart ;
    public static Position pcalEnd ;
    
    /***********************************************************************
    * The following private class variables are used in the                *
    * implementation of the Tokenize method.  They are made class          *
    * variables so they can be accessed in procedures used by              *
    * TokenizedSpec (which are defined as private class methods).          *
    *                                                                      *
    * Note: This use of static fields makes the class totally threads      *
    * unsafe.                                                              *
    ***********************************************************************/
    private static boolean inPcal ;
      // True iff we are inside a PlusCal algorithm.  inPcal => hasPcal
      // is an invariant.
    
    private static boolean canBeLabel ;
      // Set true when outputting a PlusCal token that can be followed
      // by a statement label.  Set false when outputting any other non-comment
      // PlusCal token.  The tokens that can be followed by a label are:
      //
      //    ";"  ")"  "{"   "begin"  "do"  "either" "or"  "then"  "else"
      //    "elsif" 
      //
      // It is set false by the TokenOut method and left unchanged
      // by the CommentTokenOut method (which is used to output a comment token).
    
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
      
    private static CharReader reader ;
      /*********************************************************************
      * This is the "exposed" version of the CharReader argument to the    *
      * TokenizedSpec constructor, exposed so it can be used by procedures *
      * called by Tokenize without having to be passed as an argument.     *
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

    
    private static void TokenOut(int type)
      /*********************************************************************
      * Add the token to linev and reset token to the empty string.        *
      * Reset canBeLabel.                                                  *
      *********************************************************************/
      { if (   (! token.equals(""))
            || (type == Token.STRING))
        /*******************************************************************
        * I don't remember why I thought that TokenOut can be called with  *
        * a null argument other than for the empty STRING. But, there are  *
        * no other cases of non-comment tokens with empty strings, so the  *
        * test seems harmless.                                             *
        *******************************************************************/
          { linev.addElement(new Token(token, col, type )); } ;
        if (type == Token.IDENT)
         { identHashTable.put(token, nullString);
         }
        else 
         { if (type == Token.STRING)
            { stringHashTable.put(token, nullString);
              identHashTable.put(token, nullString);
            }
           else if (type == Token.BUILTIN)
            { usedBuiltinHashTable.put(token, nullString);
            }
         };
        token = "" ;
        canBeLabel = false ;
      } ;

    private static void CommentTokenOut(int subtype)
      /*********************************************************************
      * Add the token to linev and reset token to the empty string.        *
      *********************************************************************/
      { linev.addElement(new CommentToken(token, col, subtype )); 
        token = "" ;
      } ;

    private static void startNewLine()
      /*********************************************************************
      * Append linev to vspec and reset linev.  This should be called      *
      * whenever a \n character is removed from the input stream.          *
      *********************************************************************/
      { vspec.addElement(linev)    ;
        linev = new Vector(30, 30) ;
        col = 0 ;
      } ;

    private static void TokenizingError(String msg) 
      { Debug.ReportError(
           msg + " `" + token + "' found at\n" + 
          "    line " + (reader.getLineNumber() + 1) + ", column " + 
               (col + 1));
      }
          
    private static Token[][] vspecToArray() 
      /*********************************************************************
      * Turns vspec into an array.                                         *
      *********************************************************************/
      { Token[][] aspec = new Token[vspec.size()][] ;
        int n = 0 ;                                                       
        while (n < vspec.size())                                          
          { aspec[n] =                                                     
               new Token [ ((Vector) vspec.elementAt(n)) . size() ] ;     
            int m = 0 ;                                                   
            while (m < aspec[n].length)                                    
              {aspec[n][m] =                                               
                (Token) ((Vector) vspec.elementAt(n)) . elementAt(m);     
               m = m+1;                                                   
              };                                                          
            n = n+1 ;                                                     
          };                                                              
        return aspec;
      } ;

    public static Token[][] Tokenize(CharReader charReader, int mode) 
      /*********************************************************************
      * Tokenize the input from the CharReader.                            *
      *********************************************************************/
      { vspec = new Vector(1000, 1000) ;
        reader = charReader ;
           /****************************************************************
           * This "exports" the charReader for use by the classes other    *
           * (private) methods.                                            *
           ****************************************************************/

        nextChar = reader.getNextChar();
          /*****************************************************************
          * Initialize nextChar.                                           *
          *****************************************************************/

        // Initialize PlusCal processing variables.
        hasPcal = false ;
        isCSyntax = false ;
        pcalStart = null ;
        pcalEnd = null;
        inPcal = false;
        canBeLabel = false;
        
        switch (mode)
          { 
            case MODULE    : state = PROLOG ; break ;
            case TLA       : state = START  ; break ;
            case PLUSCAL   : state = START ;
                             hasPcal = true ;
                             pcalStart = new Position(0, 0) ;
                             inPcal = true ;
                             canBeLabel = true ;
                             isCSyntax = true ;
                             break ;
            case P_PLUSCAL : state = START ;
                             hasPcal = true ;
                             pcalStart = new Position(0, 0) ;
                             inPcal = true ;
                             canBeLabel = true ;
                             break ;
            default       : Debug.ReportBug(
                             "TokenizeSpec.Tokenize called with illegal mode") ;
          } ;
        while (state != DONE)
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
                  else if (BuiltInSymbols.IsBuiltInPrefix("" + nextChar))
                    { addNextChar();
                      state = BUILT_IN ;
                    }
                  else if (nextChar == '\t')
                    { if (mode == MODULE) 
                        { Debug.ReportError(
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
                  else if (BuiltInSymbols.IsBuiltInSymbol(token))
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
                  else if (BuiltInSymbols.IsBuiltInSymbol(token))
                    { TokenOut(Token.BUILTIN) ;
                      gotoStart();
                    }
                  else 
                    { TokenizingError("Illegal lexeme ");
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
                      { 
                        reader.backspace();
                        while (! BuiltInSymbols.IsBuiltInSymbol(token))
                        { reader.backspace();
                          if (token.length() == 0)
                            { TokenizingError("Illegal lexeme");
                            };
                          token = token.substring(0, token.length()-1);
                        } ;
                        nextChar = reader.getNextChar();
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
                        { Debug.ReportError(
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
                  else if (BuiltInSymbols.IsStringChar(nextChar))
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
                    { CommentTokenOut(CommentToken.LINE) ;
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
                      Debug.Assert(cdepth >= 0,
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
                    { CommentTokenOut(CommentToken.BEGIN_OVERRUN) ;
                      skipNextChar();
                      startNewLine();
                      state = OR_COMMENT;
                    }
                  else if (nextChar == '\t')
                    { Debug.ReportError(
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
                        { CommentTokenOut(CommentToken.NORMAL);
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
                    { CommentTokenOut(CommentToken.OVERRUN) ;
                      skipNextChar();
                      startNewLine();
                      state = OR_COMMENT;
                    }
                  else if (nextChar == '\t')
                    { Debug.ReportError(
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
                      Debug.Assert(cdepth >= 0);
                      if (cdepth == 0)
                        { CommentTokenOut(CommentToken.END_OVERRUN);
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
                    { Debug.ReportError(
                         "Input ended before beginning of module");
                    }
                  else
                    { addNextChar();
                      // state = PROLOG ;
                    }
                break;

                case PROLOG_DASH :
                  Debug.Assert(token.length() <= 3) ;
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
                  Debug.ReportBug(
                    "Illegal state in TokenizeSpec.Tokenize");
                  // break;

              } ;  // ends switch
         } ; // ends while

        /*******************************************************************
        * Return the contents of vspec, as an array.                       *
        *******************************************************************/
        return vspecToArray();
      }
  
 }

/* last modified on Thu 18 Aug 2005 at 22:13:38 UT by lamport */
