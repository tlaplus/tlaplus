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
*                    a P-Syntax PlusCal algorithm.  (Called by tlatex.TeX  *
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
*    pseudoCom : A boolean that equals true iff the next comment token to  * ADDED FOR PLUSCAL
*                be output either does not end with "*)" (because it was   * ADDED FOR PLUSCAL
*                terminated by the start of a PlusCal algorithm) or does   * ADDED FOR PLUSCAL
*                not begin with a "(*" (because it immediately followed    * ADDED FOR PLUSCAL
*                the end of a PlusCal algorithm).                          * ADDED FOR PLUSCAL
*                                                                          *
*    ORCom : A boolean set when looking for the start of a PlusCal         * ADDED FOR PLUSCAL
*            algorithm when processing a comment.  It equals true if       * ADDED FOR PLUSCAL
*            processing an OR (OverRun) comment, and false if processing a * ADDED FOR PLUSCAL
*            normal comment.                                               * ADDED FOR PLUSCAL
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
*   (BuiltInPrefix)                                                        * MODIFIED for PlusCal
*     +                                                                    * MODIFIED for PlusCal
*       IF ~(inPcal /\ mode = Module)                                      * MODIFIED for PlusCal   
*         THEN                                              --> BUILT_IN   * MODIFIED for PlusCal
*         ELSEIF token = "*" /\ nextChar = ")"                             * MODIFIED for PlusCal
*           THEN    pcalEnd := getNextTokenPosition();                     * MODIFIED for PlusCal
*                   // cdepth should equal 0 here                          * MODIFIED for PlusCal
*                   inPcal := false                                        * MODIFIED for PlusCal
*                   token = "" ;                            --> START      * MODIFIED for PlusCal
*         ELSEIF isCSyntax                                                 * MODIFIED for PlusCal
*           THEN IF token = "{"                                            * MODIFIED for PlusCal
*                  THEN TokenOut(BUILTIN) ;                                * MODIFIED for PlusCal
*                       canBeLabel := true ;                               * MODIFIED for PlusCal
*                       braceDepth := braceDepth + 1        --> START      * MODIFIED for PlusCal
*                  ELSEIF token = "}"                                      * MODIFIED for PlusCal
*                    THEN TokenOut(BUILTIN) ;                              * MODIFIED for PlusCal
*                         braceDepth := braceDepth - 1                     * MODIFIED for PlusCal
*                         IF braceDepth # 0                                * MODIFIED for PlusCal
*                          THEN                             --> START      * MODIFIED for PlusCal
*                          ELSE col = ncol ;                               * MODIFIED for PlusCal
*                               inPcal := false ;                          * MODIFIED for PlusCal
*                               cdepth := 1 ;                              * MODIFIED for PlusCal
*                               pcalEnd := getNextTokenPosition() ;        * MODIFIED for PlusCal
*                               pseudoCom := true          --> COMMENT     * MODIFIED for PlusCal
*                    ELSE                                  --> BUILT_IN    * MODIFIED for PlusCal
*           ELSE                                           --> BUILT_IN    * MODIFIED for PlusCal
*   [("\t") /\ TLA mode]     --> DONE                                      *
*   [OTHER]                  --> ERROR                                     *
*                                                                          *
* ID:                                                                      *
*   [token = "WF_" or "SF_"]  TokenOut(BUILTIN)     --> START              *
*   (Letter or Digit)         +                     --> ID                 *
*   [token = "MODULE"]        TokenOut(BUILTIN);                           *
*                             mdepth := mdepth + 1  --> START              *
*   [token \in BuiltIns]                                                   * MODIFIED for PlusCal
*      IF inPcal /\ token = "algorithm" /\ ~isCsyntax /\ mode = MODULE     * MODIFIED for PlusCal
*        THEN TokenOut(BUILTIN) ;                                          * MODIFIED for PlusCal
*             col := ncol ;                                                * MODIFIED for PlusCal
*             pcalEnd := getNextTokenPosition() ;                          * MODIFIED for PlusCal
*             cdepth := 1 ;                                                * MODIFIED for PlusCal
*             inPcal := false ;                                            * MODIFIED for PlusCal
*             cbl := inPcal /\ CanPrecedeLabel(token)                      * MODIFIED for PlusCal
*             TokenOut(BUILTIN);                                           * MODIFIED for PlusCal
*             canBeLabel := cbl             --> START                      * MODIFIED for PlusCal
*   [OTHER /\ inPcal /\ canBeLabel]                                        * MODIFIED for PlusCal
*                             token1 := token       --> ID_OR_PCAL_LABEL   * MODIFIED for PlusCal
*   [OTHER]                   TokenOut(IDENT)       --> START              * MODIFIED for PlusCal
*                                                                          *
* ID_OR_PCAL_LABEL:                                                        * ADDED for PlusCal
*   \* Note: token1 contains id                                            * ADDED for PlusCal
*   (Space_Char)    +                     --> ID_OR_PCAL_LABEL             * ADDED for PlusCal
*   (":")           +  IF nextChar # "=" or ":"                            * ADDED for PlusCal
*                        THEN  token1 := token   --> PCAL_LABEL            * ADDED for PlusCal
*                        ELSE  backspace so nextChar = ":" ;               * ADDED for PlusCal
*                              token := token1;                            * ADDED for PlusCal
*                              TokenOut(IDENT)   --> START                 * ADDED for PlusCal
*   [OTHER]             token := token1;                                   * ADDED for PlusCal
*                       TokenOut(IDENT)   --> START                        * ADDED for PlusCal
*                                                                          *
* PCAL_LABEL:                                                              * ADDED for PlusCal
*   (Space_Char)    +                        --> PCAL_LABEL                * ADDED for PlusCal
*   ("+" or "-")    +  TokenOut(PCAL_LABEL)  --> START                     * ADDED for PlusCal
*   [OTHER]         token := token1;                                       * ADDED for PlusCal
*                   TokenOut(PCAL_LABEL)     --> START                     * ADDED for PlusCal
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
* NUM_OR_BI:  Needs to be fixed to handle something like \H4b2             * BUG
*   (Digit)   --> NUM                                                      * BUG
*   [OTHER]   --> BSBUILT_IN                                               * BUG
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
*             saved := CanPrecedeLabel(token)                              * MODIFIED for PlusCal
*             TokenOut(BUILTIN)                                            * MODIFIED for PlusCal
*             canBeLabel := saved                  --> START               * MODIFIED for PlusCal
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
*   [("-") /\ cdepth = 1 /\ mode = MODULE /\ ~hasPcal]                     * MODIFIED for PlusCal
*                        token1 := token;  col1 := col                     * MODIFIED for PlusCal
*                        token := "";  col := ncol (?)                     * MODIFIED for PlusCal
*                        ORCom := false ;                                  * MODIFIED for PlusCal
*                        +                              --> C_DASH         * MODIFIED for PlusCal
*   [OTHER]  IF cdepth = 1 THEN + ELSE -      --> COMMENT                  *
*                                                                          *
*                                                                          *
* COMMENT_STAR:                                                            *
*   [(")") /\ cdepth = 1] - ; depth := cdepth - 1                          *    
*                           ; TokenOut(COMMENT, NORMAL)  --> START         *
*   (")")                 - ; cdepth := cdepth - 1       --> COMMENT       *
*   [OTHER]              IF cdepth = 1                                     *
*                          THEN token := token + "*"                       *
*                          ELSE                       --> COMMENT          *
*                                                                          *
* C_DASH:                                                                  * ADDED for PlusCal
*   \* token1, col1 represents the comment on the current line preceding   * ADDED for PlusCal
*   \* the "-"; token, col is the "-"                                      * ADDED for PlusCal
*   ("-")      +                            --> C_DASH_DASH                * ADDED for PlusCal
*   [OTHER]    \* this case modified by LL on 12 April 2013 to fix a bug   *
*              \* that occurred if the single "-" was followed by "\n"     *
*              \* or "*)".                                                 *
*              token := token1 \o token;                                   * ADDED for PlusCal
*              col := col1  --> IF ORCom THEN OR_COMMENT                   * ADDED for PlusCal
*                                        ELSE COMMENT                      * ADDED for PlusCal
*                                                                          *
* C_DASH_DASH:                                                             * ADDED for PlusCal 
*   (Letter)    + --> C_DASH_DASH                                          * ADDED for PlusCal
*   [OTHER]   IF token \in {"--fair", "--algorithm"}                       * ADDED for PlusCal
*               THEN IF token1 # all spaces                                * ADDED for PlusCal
*                      THEN pseudoCom := true;                             * ADDED for PlusCal
*                           token2 := token; col2 := col;                  * ADDED for PlusCal
*                           token := token1; col := col1;                  * ADDED for PlusCal
*                           TokenOut(COMMENT, IF ORCom THEN END_OVERRUN    * ADDED for PlusCal
*                                                      ELSE NORMAL )       * ADDED for PlusCal
*                           token := token2; col := col2;                  * ADDED for PlusCal
*                    FI;                                                   * ADDED for PlusCal
*                    hasPcal := true;                                      * ADDED for PlusCal
*                    pcalStart := getNextTokenPosition();                  * ADDED for PlusCal
*                    isAlgorithm := (token = "--algorithm");               * ADDED for PlusCal
*                    TokenOut(BUILTIN);                                    * ADDED for PlusCal
*                    SkipSpacesAndNewlines();                              * ADDED for PlusCal
*                    IF isAlgorithm THEN             --> GET_ALG_NAME      * ADDED for PlusCal
*                                   ELSE             --> GET_ALG_TOKEN     * ADDED for PlusCal
*               ELSE token := token1 \o token                              * ADDED for PlusCal     
*                    col := col1                     --> COMMENT           * ADDED for PlusCal
*                                                                          *
* GET_ALG_TOKEN:                                                           * ADDED for PlusCal
*   (Letter)  +    --> GET_ALG_TOKEN                                       * ADDED for PlusCal
*   [OTHER]  IF token = "algorithm"                                        * ADDED for PlusCal
*              THEN TokenOut(BUILTIN) ;                                    * ADDED for PlusCal
*                   SkipSpacesAndNewlines() --> GET_ALG_NAME               * ADDED for PlusCal
*              ELSE \* Bad input; interpret everything else as comment     * ADDED for PlusCal
*                   pcalEnd := getNextTokenPosition();                     * ADDED for PlusCal
*                   pseudoCom := true       --> COMMENT                    * ADDED for PlusCal
*                                                                          * 
* GET_ALG_NAME:                                                            * ADDED for PlusCal
*   (Letter)  +    --> GET_ALG_NAME                                        * ADDED for PlusCal
*   (Digit)   +    --> GET_ALG_NAME                                        * ADDED for PlusCal
*   [OTHER]   IF token # "" /\ contains a letter                           * ADDED for PlusCal
*               THEN TokenOut(IDENT);                                      * ADDED for PlusCal
*                    SkipSpacesAndNewlines();                              * ADDED for PlusCal
*                    isCSyntax := (nextChar = "{");                        * ADDED for PlusCal
*                    + TokenOut(BUILTIN);                                  * ADDED for PlusCal
*                    cdepth := 0 ;                                         * ADDED for PlusCal
*                    inPcal := true;                                       * ADDED for PlusCal
*                    braceDepth := 0                 --> START             * ADDED for PlusCal
*               ELSE pcalEnd := getNextTokenPosition();                    * ADDED for PlusCal
*                    pseudoCom := true               --> COMMENT           * ADDED for PlusCal
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
*   [("-") /\ cdepth = 1 /\  mode = MODULE /\ ~hasPcal]                    * ADDED for PlusCal
*                        token1 := token;  col1 := col                     * ADDED for PlusCal
*                        token := "";  col := ncol (?)                     * ADDED for PlusCal
*                        ORCom := true ;                                   * ADDED for PlusCal
*                        +                              --> C_DASH         * ADDED for PlusCal
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

import pcal.MappingObject.EndTLAToken;
import pcal.PCalLocation;

/**
 * @author lamport
 *
 */
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
     *   pcalEnd   : The Positions of the first token of PlusCal code and the
     *               position immediately after the last token of the PlusCal
     *               code.  More precisely, pcalEnd is set to a position that 
     *               is > the position of the last token of the PlusCal code
     *               and =< the position of the first token after the PlusCal
     *               code.  If the last PlusCal token has Position (i, j), then
     *               pcalEnd is probably (i, j+1), even if the last token on
     *               line i has position j.
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
    
    private static boolean pseudoCom ;
      // Set true iff the next Comment token to be output did not have
      // two of its delimiter characters because it immediately preceded or
      // followed a PlusCal algorithm.  Set false by CommentTokenOut
    
    private static boolean ORCom ;
      // Set true when looking for the start of a Pluscal algorithm when
      // processing a comment--true if processing an OR (overrun) comment,
      // false if processing a normal comment.  
    
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
      private static final int ID_OR_PCAL_LABEL   = 36 ;
      private static final int PCAL_LABEL         = 37 ;
      private static final int C_DASH             = 38 ;
      private static final int C_DASH_DASH        = 39 ;
      private static final int GET_ALG_TOKEN      = 40 ;
      private static final int GET_ALG_NAME       = 41 ;      
      
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
      { linev.addElement(new CommentToken(token, col, subtype, pseudoCom)); 
        pseudoCom = false;
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

    private static void SkipSpaceAndNewlines() {
        boolean notDone = true ;
        while (notDone) {
            while (Misc.IsSpace(nextChar)) {
                skipNextChar() ;
            }
            if (nextChar == '\n') {
                skipNextChar() ;
                startNewLine() ;
            }
            else {
                notDone = false ;
            }
            col = ncol;
            token = "" ;
        }
       
    }
    /**
     * Returns the Position in the final output of the next
     * token to be output.
     * 
     * @return
     */
    private static Position getNextTokenPosition() {
        return new Position(vspec.size(), linev.size());
    }
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
        pseudoCom = false;
        ORCom = false;
        
        /*
         * braceDepth is the current { } brace nesting depth while processing
         * a C-Syntax PlusCal algorithm.
         */
        int braceDepth = 0 ;
        
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
                  else if (BuiltInSymbols.IsBuiltInPrefix("" + nextChar, inPcal))
                    { addNextChar();
                      if (!(inPcal && (mode == MODULE))) {
                        state = BUILT_IN ;
                      }
                      else if (token.equals("*") && (nextChar == ')')){
                          pcalEnd = getNextTokenPosition() ;
                          inPcal = false ;
                          token = "" ;
                          gotoStart() ;
                      }
                      else if (isCSyntax) {
                          if (token.equals("{")) {
                              TokenOut(Token.BUILTIN);
                              canBeLabel = true ;
                              braceDepth++ ;
                              gotoStart() ;
                          }
                          else if (token.equals("}")) {
                              TokenOut(Token.BUILTIN);
                              braceDepth-- ;
                              if (braceDepth != 0) {
                                  gotoStart() ;
                              }
                              else {
                                  col = ncol ;
                                  inPcal = false ;
                                  cdepth = 1 ;
                                  pcalEnd = getNextTokenPosition() ;
                                  pseudoCom = true ;
                                  state = COMMENT ;
                              }
                          }
                          else {
                              state = BUILT_IN ;
                          }
                      }
                      else {
                          state = BUILT_IN ;
                      }
                      // old: addNextChar();
                      // old: state = BUILT_IN ;
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
                  else if (BuiltInSymbols.IsBuiltInSymbol(token, inPcal))
                    { if (token.equals("MODULE")) 
                        { mdepth = mdepth + 1; 
                          TokenOut(Token.BUILTIN) ;
                          gotoStart();
                        }
                      else if (inPcal && token.equals("algorithm") 
                                && !isCSyntax && (mode == MODULE)) {
                          TokenOut(Token.BUILTIN) ;
                          col = ncol; 
                          pcalEnd = getNextTokenPosition() ;
                          cdepth = 1 ;
                          inPcal = false ;
                          pseudoCom = true ;
                          state = COMMENT ;
                      }
                      else {
                          boolean cbl = inPcal && BuiltInSymbols.CanPrecedeLabel(token) ;
                          TokenOut(Token.BUILTIN) ;
                          canBeLabel = cbl ;
                          gotoStart();
                      }
                    }
                  else if (inPcal && canBeLabel) {
                      token1 = token ;
                      col1   = col ;   // This should be unnecessary
                      state = ID_OR_PCAL_LABEL ;
                  }
                  else 
                    { TokenOut(Token.IDENT) ;
                      gotoStart();
                    };
                  break;          
                case ID_OR_PCAL_LABEL :
                    while (Misc.IsSpace(nextChar)) {
                        addNextChar();
                    }
                    if (nextChar == ':') {
                        addNextChar();
                        if ((nextChar != '=') && (nextChar != ':')) {
                            token1 = token ;
                            state = PCAL_LABEL ;
                        }
                        else {
                            reader.backspace() ;
                            ncol--;
                            nextChar = ':' ;
                            token = token1 ;
                            TokenOut(Token.IDENT) ;
                            gotoStart() ;
                        }  
                    } 
                    else {
                        token = token1 ;
                        TokenOut(Token.IDENT) ;
                        gotoStart() ;
                    }
                  break;
                  
                case PCAL_LABEL :
                    while (Misc.IsSpace(nextChar)) {
                        addNextChar();
                    }
                    if ((nextChar == '+') || (nextChar == '-')) {
                        addNextChar() ;
                        TokenOut(Token.PCAL_LABEL) ;
                        gotoStart() ;
                    }
                    else {
                        token = token1 ;
                        TokenOut(Token.PCAL_LABEL) ;
                        gotoStart() ;
                    }
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
                           // "\" symbols are never PCal symbols 
                    { TokenOut(Token.BUILTIN) ;
                      gotoStart();
                    }
                  else 
                    { TokenizingError("Illegal lexeme ");
                    } ;
                   break;

                case BUILT_IN :
                  if (BuiltInSymbols.IsBuiltInPrefix(token + nextChar, inPcal))
                    { addNextChar();
                      // state = BUILT_IN;
                    }
                  else 
                    { 
                     if (! BuiltInSymbols.IsBuiltInSymbol(token, inPcal))
                      { 
                        reader.backspace();
                        while (! BuiltInSymbols.IsBuiltInSymbol(token, inPcal))
                        { reader.backspace();
                          if (token.length() == 0)
                            { TokenizingError("Illegal lexeme");
                            };
                          token = token.substring(0, token.length()-1);
                        } ;
                        nextChar = reader.getNextChar();
                      } ;
                      boolean saved = BuiltInSymbols.CanPrecedeLabel(token) ;
                      TokenOut(Token.BUILTIN) ;
                      canBeLabel = saved ;
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
                  else if ((nextChar == '-') && (cdepth == 1)
                             && (mode == MODULE) && !hasPcal) {
                      token1 = token;
                      col1 = col;
                      token = "" ;
                      col = ncol ;
                      ORCom = false;
                      addNextChar() ;
                      state = C_DASH ;
                    }
                  else
                    { if (cdepth == 1) {addNextChar();}
                        else {skipNextChar();};
                      // state = COMMENT ;
                    }
                  break;

                case COMMENT_STAR :      
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

                case C_DASH : 
                    // token1, col1 describes the comment preceding the "-"
                    if (nextChar == '-') {
                        addNextChar() ;
                        state = C_DASH_DASH ;
                    }
                    else {
                         // Bug fix of 12 Apr 2013 by LL.
                         // Appending the next character to the current
                         // token causes an error if the next token is the "*" of
                         // a "*)" or is a '\n'.  So, I commented out the
                         // adNextChar().  I also changed the assignment to state
                         // to go to the right place depending on whether or not
                         // this is an OR_COMMENT.  I don't know why the previous code
                         // didn't do that.
                         token = token1 + token ;
                         col = col1;
                        // addNextChar();
                        // state = COMMENT;
                        state = ORCom ? OR_COMMENT : COMMENT ;
                    }
                  break ;
                  
                case C_DASH_DASH :
                  while (Misc.IsLetter(nextChar)) {
                      addNextChar() ;
                  }
                  boolean isAlgorithm = token.equals("--algorithm") ;
                  if (isAlgorithm || token.equals("--fair")) {
                      if (! Misc.isBlank(token1)) {
                          pseudoCom = true;
                          token2 = token;
                          col2 = col;
                          token = token1;
                          col = col1;
                          CommentTokenOut(ORCom?CommentToken.END_OVERRUN:CommentToken.NORMAL) ;
                          token = token2;
                          col = col2;
                      }
                      hasPcal = true;
                      pcalStart = getNextTokenPosition();
                      TokenOut(Token.BUILTIN);
                      SkipSpaceAndNewlines();
                      if (isAlgorithm) {
                          state = GET_ALG_NAME ;
                      }
                      else {
                          state = GET_ALG_TOKEN ;
                      }                      
                  }
                  else {
                      token = token1 + token ;
                      col = col1 ;
                      state = COMMENT ;
                  }
                  break ;
                  
                case GET_ALG_TOKEN :
                  while (Misc.IsLetter(nextChar)) {
                      addNextChar();
                  }
                  if (token.equals("algorithm")) {
                      TokenOut(Token.BUILTIN) ;
                      SkipSpaceAndNewlines() ;
                      state = GET_ALG_NAME ;
                  }
                  else {
                      pcalEnd = getNextTokenPosition() ;
                      pseudoCom = true ;
                      state = COMMENT ;
                  }
                  break ;
                  
                case GET_ALG_NAME :
                  while (Misc.IsLetter(nextChar) || Misc.IsDigit(nextChar)) {
                      addNextChar() ;                      
                  }
                  if (Misc.hasLetter(token)) {
                      TokenOut(Token.IDENT) ;
                      SkipSpaceAndNewlines() ;
                      isCSyntax = (nextChar == '{') ;
                      cdepth = 0 ;
                      inPcal = true ;
                      braceDepth = 0 ;
                      gotoStart() ;
                  } 
                  else {
                      pcalEnd = getNextTokenPosition() ;
                      pseudoCom = true ;
                      state = COMMENT ;
                      
                  }
                  break ;
                
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
                  else if ((nextChar == '-') && (cdepth == 1) 
                              && (mode == MODULE) && ! hasPcal) {
                      token1 = token ;
                      col1 = col ;
                      token = "" ;
                      col = ncol ;
                      ORCom = true ;
                      addNextChar() ;
                      state = C_DASH ;
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

        /*
         * Prevent null pointer exception in PlusCal algorithm that was
         * not ended.
         */
        if (hasPcal) {
            if (pcalEnd == null) {
                pcalEnd = new Position(Integer.MAX_VALUE, 0) ;
            }
        }
        /*******************************************************************
        * Return the contents of vspec, as an array.                       *
        *******************************************************************/
        return vspecToArray();
      }
    
    /**
     * The argument spec is the current tokenized specification, generated
     * by the Tokenize method.  If that spec has a C-Syntax PlusCal algorithm,
     * this method turns "(", ")", "{", and "}" tokens that are PlusCal
     * delimiters (rather than parts of an expression) into the corresponding
     * tokens that produce the appropriate TeX output.  
     * 
     * A PlusCal "(" can follow the following:
     *   "macro" + IDENT
     *   "procedure" + an IDENT 
     *   "process" | "if" | "while" | "with"
     * 
     * A PlusCal "{" other than the initial one can follow the following:
     *   a PlusCal "{"
     *   a PlusCal ")"
     *   "else" | "either" | "or" | "define"
     *   "variable[s]" [<expression> [, | ;]]^+ 
     *   ";"  
     *   PCAL_LABEL
     * 
     * This method also removes an extra gray bar that can appear after
     * the algorithm when using the -shade and -noPcalShade options.
     * 
     * The isTeX argument is true if this is called for tla2tex.TeX, in 
     * which case the spec can start anywhere inside a PlusCal algorithm.
     * 
     * @param spec
     * @param isTeX  true for tla2tex.TeX, false for tla2tex.TLA
     */
    public static void FixPlusCal(Token[][] spec, boolean isTeX) {
//        if ((!hasPcal) || (!isCSyntax)) {
//            return ;
//        }
       
        if (!hasPcal) {
            return ;
        }
        
        // Fix the problem of an extra gray bar caused by an empty
        // comment token following the algorithm by removing that
        // comment if it exists.
        if (    Parameters.CommentShading
            && Parameters.NoPlusCalShading
            && (pcalEnd.line < spec.length)
            && (pcalEnd.item < spec[pcalEnd.line].length)) {
            Token tok = pcalEnd.toToken(spec) ;
            if (tok.type == Token.COMMENT) {
                CommentToken ctok = (CommentToken) tok ;
                if (ctok.string.trim().equals("") ) {
                  int rsubtype = ctok.rsubtype ;
                  
                  // Set newline to spec[pcalEnd.line] with element pcalEnd.item 
                  // removed.
                  Token[] newline = new Token[spec[pcalEnd.line].length - 1] ;
                  int j = 0 ;
                  for (int i = 0 ; i < spec[pcalEnd.line].length ; i++) {
                     if (i != pcalEnd.item) {
                         newline[j] = spec[pcalEnd.line][i] ;
                         j++ ;
                     }
                  }                  
                  if (rsubtype == CommentToken.NORMAL) {
                     spec[pcalEnd.line] = newline ;
                  }
                  else {
                      if (rsubtype == CommentToken.BEGIN_OVERRUN) {
                          // The following lines of the spec should consist
                          // of a (possibly empty) sequence of 1-token lines
                          // containing comment tokens of rsubtype OVERRUN followed
                          // by a line beginning with a comment token of rsubtype
                          // END_OVERRUN.  If all those comment tokens have only
                          // blank strings, then we want to delete all of them.
                          //
                          // We begin by setting nextLine to the first line following
                          // pcalEnd.line that does not contain an OVERRUN token with
                          // a blank string and we set next to the first token on that
                          // line--or null if for some strange reason that line has
                          // no tokens.
                          Token next = spec[pcalEnd.line + 1][0] ;
                          int nextLine = pcalEnd.line + 1;
                          while (   (next != null)
                                 && (next.type == CommentToken.COMMENT)
                                 && (((CommentToken) next).rsubtype == CommentToken.OVERRUN)
                                 && (next.string.trim().equals(""))
                                  ) {
                              nextLine++ ;
                              if (spec[nextLine+1].length > 0) {
                                  next = spec[nextLine][0];
                              } 
                              else {
                                  next = null ;
                              }
                          }
                          if (   (next != null)
                              && (next.type == CommentToken.COMMENT)
                              && (next.string.trim().equals(""))
                              && (((CommentToken) next).rsubtype == CommentToken.END_OVERRUN)
                              ) {
                              
                              // We have an empty comment that we should remove .
                              // First, we remove the first comment token, 
                              spec[pcalEnd.line] = newline ;
                              
                              // next we remove all the OVERRUN tokens.
                              for (int i = pcalEnd.line + 1 ; i < nextLine ; i++) {
                                  spec[i] = new Token[0] ;
                              }
                                  
                              // next we remove the END_OVERRUN token
                              newline = new Token[spec[nextLine].length-1]  ;                                  
                              System.arraycopy(spec[nextLine], 1, newline, 
                                                      0, spec[nextLine].length - 1) ;
                              spec[nextLine] = newline ;
                          } 
                      }
                  }
                }
            }
        }
              
        if (!isCSyntax) {
            return ;
        }
        // If isTeX is false, or the first token is --algorithm or --fair,
        // then we're at the beginning of the algorithm, 
        // and the first "{" that's not a comment is the first PlusCal "{".
        Position pos = pcalStart ;
        boolean beginningOfAlgorithm = ! isTeX ;
        if (isTeX &&  pos != null) {
            String firstString = pos.toToken(spec).string ;
            if (firstString.equals("--algorithm") || firstString.equals("--fair")) {
                beginningOfAlgorithm = true ;
            }
        }

        if (beginningOfAlgorithm) {
           while (   (pos != null) 
                  && (   (pos.toToken(spec).type != Token.BUILTIN)
                      || (! pos.toToken(spec).string.equals("{")))) {            
              pos = nextTokenPos(pos, spec) ;
           }
        }

        // pos should not be null, but...
        if (pos != null) {
         pos = ProcessPcalBrace(pos, spec, isTeX) ;
         // System.out.println("pos = " + pos.toString()) ;
        }
        
        // For tla2tex.TeX, we want to keep going until we
        // get to the end of the input.
        while (isTeX && (pos != null)) {
            pos = ProcessPcalBrace(pos, spec, isTeX) ;
        }
    }
    
    /**
     * ProcessPcalBrace(Position pos, Token[][] spec, boolean isTeX)
     * ----------------------------------------------
     * 
     * If isTeX is false, then assumes that it is called with pos the position 
     * of a left brace token in spec that is a PlusCal delimiter.  It converts 
     * all PlusCal delimiters from (and including) that left brace through
     * the matching right brace to the appropriate tokens, and returns the
     * position of the next token past the matching right brace.  If
     * there is no matching right brace, it returns  null.
     *   
     * If isTeX is true, then it processes all tokens in spec, returning
     * null.  If the first character is a left brace,
     * it assumes it's a PlusCal left brace.  
     * 
     * Here's a spec for this, in a style similar to that for Tokenize.
     * Here,  ++ means go to next non-comment token.  It starts in
     * state START if isTeX is false, and in NOT_LBRACE if it's true.
     * 
     * START:
     *   make current token pcalLBrace ++ --> CAN_BE_LBRACE
     *   
     * CAN_BE_LBRACE:
     *   (BUILT_IN "{")   ProcessPcalBrace(pos, spec) --> NOT_LBRACE
     *   [OTHER]     --> NOT_LBRACE
     * 
     * NOT_LBRACE:
     *   (PCAL_LABEL)                           ++ --> CAN_BE_LBRACE
     *   (BUILT_IN & ";", "else", "either","or", "define") ++ --> CAN_BE_LBRACE
     *   (BUILT_IN & "}") make current token pcalRBrace    ++ return current position
     *   (BUILT_IN & LEFT_PAREN) ++ skipToUnmatchedEnd(pos, spec, false)
     *                           ++ ---> NOT_LBRACE
     *   (BUILT_IN & "variable[s]") ++ ---> AFTER_VAR_DECL
     *   (BUILT_IN & "process" | "if" | "while" | "with") ++ --> SEEKING_LPAREN
     *   (BUILT_IN & "procedure" | "macro") ++ ---> SEEKING_IDENT_LPAREN
     *   [OTHER] ++ ---> NOT_LBRACE
     *   
     * SEEKING_LPAREN:
     *   (BUILT_IN & "(") fix current token
     *         skipToUnmatchedEnd(pos, spec, false)
     *         IF current token = ")" THEN fix it
     *                                ELSE bad PlusCal code
     *         ++ ---> CAN_BE_LBRACE
     *         
     *   [OTHER] bad PlusCal code
     *           ++ ---> NOT_LBRACE 
     *           
     * SEEKING_IDENT_LPAREN:
     *   (IDENT) ++ ---> SEEKING_LPAREN
     *   [OTHER]  bad PlusCal code
     *            ++ ---> NOT_LBRACE 
     *            
     * AFTER_VAR_DECL:
     *   (BUILT_IN & "," | ";") ++ ---> AFTER_COMMA
     *   (BUILT_IN & LEFT_PAREN) ++ skipToUnmatchedEnd(pos, spec, false)
     *                           ++ ---> AFTER_VAR_DECL
     *   [OTHER] ++ ---> AFTER_VAR_DECL
     *   
     * AFTER_COMMA:
     *   (BUILT_IN & "{") ProcessPcalBrace(pos, spec) --> NOT_LBRACE
     *   (BUILT_IN & "define" | "macro" | "procedure" | "fair" | "process")
     *      ---> NOT_LBRACE
     *   [OTHER] ---> AFTER_VAR_DECL
     *   
     * @param pos
     * @param spec
     * @return
     */
    private static final int CAN_BE_LBRACE         = 1 ;
    private static final int NOT_LBRACE            = 2 ;
    private static final int SEEKING_LPAREN        = 3 ;
    private static final int SEEKING_IDENT_LPAREN  = 4 ;
    private static final int AFTER_VAR_DECL        = 5 ;
    private static final int AFTER_COMMA           = 6 ;
    
    public static Position ProcessPcalBrace(Position pos, Token[][] spec, boolean isTeX) {
        Token tok = pos.toToken(spec) ;
        Position curPos = pos ;
        if (!isTeX) {
            tok.string = BuiltInSymbols.pcalLeftBrace ;
            curPos = nextNonComment(pos, spec) ;
        }
        int pstate = CAN_BE_LBRACE ;  
        
        while (curPos != null) {
            tok = curPos.toToken(spec) ;
            switch (pstate) {
            case CAN_BE_LBRACE :
                if ((tok.type == Token.BUILTIN) && tok.string.equals("{")) {
                 curPos = ProcessPcalBrace(curPos, spec, false) ;   
                }
                else {
                    pstate = NOT_LBRACE ;
                }
                break ;

            case NOT_LBRACE :
                if (tok.type == Token.PCAL_LABEL) {
                    pstate = CAN_BE_LBRACE ;
                }
                else if (tok.type == Token.BUILTIN) {
                         if ( (tok.string.equals(";"))
                         || (tok.string.equals("else"))
                         || (tok.string.equals("either"))
                         || (tok.string.equals("or"))
                         || (tok.string.equals("define"))
                        ) {
                            pstate = CAN_BE_LBRACE ;
                          }
                          else if (tok.string.equals("}")) {
                              tok.string = BuiltInSymbols.pcalRightBrace ;
                              return nextNonComment(curPos, spec);
                          }
                          else if (BuiltInSymbols.GetBuiltInSymbol(
                                     tok.string, true).symbolType == Symbol.LEFT_PAREN) {
                              curPos = skipToUnmatchedEnd(nextNonComment(curPos, spec), 
                                                          spec, false) ;
                          }
                          else if (   tok.string.equals("variable")
                                   || tok.string.equals("variables")) {
                            pstate = AFTER_VAR_DECL ;  
                          }
                          else if (   tok.string.equals("if")
                                   || tok.string.equals("while")
                                   || tok.string.equals("with")
                                   || tok.string.equals("process")
                                  ) {
                            pstate = SEEKING_LPAREN ;  
                          }
                          else if (   tok.string.equals("procedure")
                                  || tok.string.equals("macro")
                                 ) {
                           pstate = SEEKING_IDENT_LPAREN ;  
                         }
                }
                curPos = nextNonComment(curPos, spec);
                break ;

            case SEEKING_LPAREN :
                if ((tok.type == Token.BUILTIN) && tok.string.equals("(")) {
                    tok.string = BuiltInSymbols.pcalLeftParen ;
                    curPos = skipToUnmatchedEnd(nextNonComment(curPos, spec), spec, false) ;
                    if (curPos != null) {
                        tok = curPos.toToken(spec) ;
                        if ((tok.type == Token.BUILTIN) && tok.string.equals(")")) {
                            tok.string = BuiltInSymbols.pcalRightParen ;
                        }
                        else {
                            // The PlusCal code is bad.  We ignore it.
System.out.println("Error SEEKING_LPAREN at " + curPos.toString());
                        }
                    }
                    pstate = CAN_BE_LBRACE ;
                }
                else {
                    // Bad PlusCal code. Ignore it.
System.out.println("Error SEEKING_LPAREN(2) at " + curPos.toString());
                    pstate = NOT_LBRACE ;
                }
                curPos = nextNonComment(curPos, spec);
                break ;

            case SEEKING_IDENT_LPAREN :
                if (tok.type == Token.IDENT) {
                    pstate = SEEKING_LPAREN ;
                } 
                else {
                    // The PlusCal code is bad.  We ignore it.
System.out.println("Error SEEKING_IDENT_LPAREN at " + curPos.toString());
                    pstate = NOT_LBRACE ;
                }
                curPos = nextNonComment(curPos, spec); 
                break ;

            case AFTER_VAR_DECL :
                if (   (tok.type == Token.BUILTIN) 
                    && (   tok.string.equals(",")
                        || tok.string.equals(";"))) {
                    pstate = AFTER_COMMA ;
                }
                else if (     (tok.type == Token.BUILTIN) 
                           && (BuiltInSymbols.GetBuiltInSymbol(
                                     tok.string, true).symbolType == Symbol.LEFT_PAREN)) {
                    curPos = skipToUnmatchedEnd(nextNonComment(curPos, spec), 
                                                spec, false) ;
                }    
                curPos = nextNonComment(curPos, spec); 
                break ;

            case AFTER_COMMA :
                if ((tok.type == Token.BUILTIN) && tok.string.equals("{")) {
                    curPos = ProcessPcalBrace(curPos, spec, false) ;   
                    pstate = NOT_LBRACE ;
                   }
                else if (   (tok.type == Token.BUILTIN) 
                         && (   tok.string.equals("define")
                             || tok.string.equals("macro")
                             || tok.string.equals("procedure")
                             || tok.string.equals("fair")
                             || tok.string.equals("process")
                            )) {
                            pstate = NOT_LBRACE ;
                        }
                else {
                    pstate = AFTER_VAR_DECL ;
                }
                break ;
                
            default :
                Debug.ReportBug("Impossible case in TokenizeSpec.ProcessPcalBrace") ;
            }

        }
        return curPos;
    }
    /**
     * Returns the position of the next token after position pos in
     * specification spec if that token exists and is in the PlusCal
     * algorithm; otherwise, it returns null.  For convenience it returns
     * null if called with a null pos argument.
     * 
     * @param pos
     * @param spec
     * @return
     */
   private static Position nextTokenPos(Position pos, Token[][] spec) {
      if (pos == null) {
          return null ;
      }
      int nextItem = pos.item + 1;
      if (   (nextItem < spec[pos.line].length)
          && (   (pos.line < pcalEnd.line)
              || (nextItem < pcalEnd.item))) {
          return new Position(pos.line, nextItem) ;
      }
      int nextLine = pos.line + 1 ;
      while ((nextLine < spec.length) && (spec[nextLine].length == 0)) {
          nextLine++;
      }
      if (   (nextLine < spec.length)
          && (   (nextLine < pcalEnd.line)
              || (   (nextLine == pcalEnd.line)
                  && (0 < pcalEnd.item)))) {
          return new Position(nextLine, 0) ;
      }
      return null;
  }

   /**
    * Returns the position of the next token after position pos in
    * specification spec that is not a comment, if that token exists and is 
    * in the PlusCal algorithm; otherwise, it returns null.  
    * For convenience it returns null if called with a null pos argument.
    * 
    * @param pos
    * @param spec
    * @return
    */
   
   private static Position nextNonComment(Position pos, Token[][] spec) {
       Position nextPos = nextTokenPos(pos, spec) ;
       while (  (nextPos != null)
               && (nextPos.toToken(spec).type == Token.COMMENT)) {
           nextPos = nextTokenPos(nextPos, spec);
       }
       return nextPos ;
   }
   
   /**
    * Starting from position pos, it skips to an ending token, leaving 
    * pos pointing to it.  It returns null if there is no such token.
    * An ending token is an unmatched RIGHT_PAREN or, if punct is true,
    * a "," or ";"
    * 
    * @param pos    The position of the token.
    * @param spec   The specification.
    * @param punct  True if stopping at comma or semicolon.
    * @return
    */
   public static Position skipToUnmatchedEnd(
                             Position pos, Token[][] spec, boolean punct) {
       Position nextPos = pos ;
       while (nextPos != null) {
           Token tok = nextPos.toToken(spec) ;
           if (tok.type == Token.BUILTIN) {
               int symType = BuiltInSymbols.GetBuiltInSymbol(
                                 tok.string, true).symbolType ;
               if (   (symType == Symbol.RIGHT_PAREN)
                   || (   punct
                       && (   tok.string.equals(";") 
                           || tok.string.equals(",")))) {
                   return nextPos;
               }
               if (symType == Symbol.LEFT_PAREN) {
                   nextPos = nextNonComment(nextPos, spec) ;
                   nextPos = skipToUnmatchedEnd(nextPos, spec, false);
               }
           }           
           nextPos = nextNonComment(nextPos, spec);
       }       
       return null ;
   }
  }

/* last modified on Thu 18 Aug 2005 at 22:13:38 UT by lamport */
