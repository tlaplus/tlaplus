// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS FormatComments                                                     *
*                                                                          *
* A that provides the following methods having to do with the formating    *
* of comments:                                                             *
*                                                                          *
* WriteComment(writer, vec, commentType, indentOrWidth, tlaMode)           *
*    Writes the comment, which is represented as a vector vec of the       *
*    strings that form the lines of the comment.  The tlaMode argument     *
*    determines if the comments are to be formatted (true), or treated     *
*    as raw LaTeX input (false).                                           *
*                                                                          *
* Initialize                                                               *
*    Initializes the tables used by the methods.                           *
*                                                                          *
* IsWord(str)                                                              *
*    True iff str is in the list of common English words.                  *
*                                                                          *
* isAmbiguous(str)                                                         *
*    True iff str is a built-in symbol that can also appear as             *
*    ordinary punctuation.                                                 *
*                                                                          *
* isRepeatChar(ch)                                                         *
*    True iff ch is a character like "~", a sequence of which is           *
*    treated as a single token.                                            *
*                                                                          *
* getRepeatCharMin(ch)                                                     *
*    If ch is a repeat character, then this is the minimum number of       *
*    ch characters regarded as a single repeated-sequence token.           *
*                                                                          *
* ------------------------------------------------------------------------ *
*                                                                          *
* THINGS POSSIBLY TO CLEAN UP:                                             *
*                                                                          *
* - If "foo" and "bar" are determined not to be TLA tokens, then           *
*   "foo (+) bar" has more space around the (+) than if they were          *
*   TLA tokens.  Should this be fixed?                                     *
*                                                                          *
* - Various built-in symbols should produce different output when          *
*   used in a comment.  What they should produce depends on the            *
*   context.  For example,                                                 *
*                                                                          *
*   * ELSE, LET, and IN  shouldn't have extra space around them            *
*     if they're not part of a TLA expression.  In fact, it might          *
*     be better to type them in Roman, since they could be part            *
*     of a title.                                                          *
*                                                                          *
*   * IN should probably have extra space after it in a TLA expression     *
*     only if it begins the line.                                          *
*                                                                          *
*   At the moment, this doesn't seem worth bothering with.                 *
*                                                                          *
* - The program does a pretty hackish job of formatting shaped             *
*   paragraphs, essentially just starting a new paragraph when it          *
*   thinks the text should start on a new line.  Should we try to do       *
*   some clever alignment, using tabular environments?                     *
*                                                                          *
* - It currently typesets most all-uppercase words like symbols,           *
*   in italics.  Should this be changed so an all upper-case English       *
*   word is typeset in Roman or small caps.  (The latter would             *
*   work reasonably well if the user types "WOMEN IN LOVE", and            *
*   the "IN" is typeset as a TLA built-in symbol.                          *
***************************************************************************/
package tla2tex;
import java.util.Hashtable;
import java.util.Vector;

public final class FormatComments
{ public static void WriteComment(OutputFileWriter writer, 
                                  Vector           vec, 
                                  int              commentType,
                                  float            indentOrWidth,
                                  boolean          tlaMode )
    /***********************************************************************
    * Writes the comment to the writer.                                    *
    *                                                                      *
    *    vec: A vector of the strings that form the lines of the           *
    *         comment.                                                     *
    *                                                                      *
    *    commentType: The type of comment.                                 *
    *                                                                      *
    *    indentOrWidth: For a multi-line comment, either the               *
    *      amount it is to be indented, or its width, depending            *
    *      on the commentType.                                             *
    *                                                                      *
    *                                                                      *
    * The possible commentTypes, and the meaning of the indentOrWidth      *
    * argument for them, is as follows:                                    *
    *                                                                      *
    *   ONE_LINE                                                           *
    *     A one-line comment typeset in LR mode.  The other arguments      *
    *     are ignored.  For this commentType, the com argument must have   *
    *     at most one line.                                                *
    *                                                                      *
    *   ZERO_WIDTH                                                         *
    *     Like ONE-LINE, except it is typeset as a zero-width box.         *
    *                                                                      *
    *   PAR                                                                *
    *     A multi-line comment typeset in paragraph mode as a              *
    *     sequence of paragraphs indented indentOrWidth points             *
    *     from the left margin using the LaTeXCommentPar                   *
    *     environment.  However, if indentOrWidth < -1,                    *
    *     then the indentation is determined by the minimum                *
    *     number of spaces at the beginning of lines.                      *
    *                                                                      *
    *   RIGHT_MULTI                                                        *
    *     A multi-line comment typeset as a zero-depth box                 *
    *     of width indentOrWidth points, using the                         *
    *     LaTeXRightMultiLineComment environment.                          *
    *                                                                      *
    * The tlaMode argument is true iff this is called for the tlatex.TLA   *
    * program; it is false if called for the tlatex.TeX program.           *
    *                                                                      *
    * This will start writing on a new line, so the caller must be careful *
    * to end the previous output line with a "%" if necessary to avoid     *
    * adding an unwanted space in the TeX output.                          *
    ***********************************************************************/
    { 
      /*********************************************************************
      * Tokenize the comment.                                              *
      *********************************************************************/
      CToken[][] tokens = null ;
      if(tlaMode)
        { tokens = TokenizeComment.Tokenize(vec);
        }
      else
        { tokens = TokenizeComment.TeXTokenize(vec);
        } ;

      if (tokens == null) { return; };
        /*******************************************************************
        * Return if called with a null comment (one having no lines).      *
        * This can happen if the input contains a (*******) not followed   *
        * by any aligned comment lines, in which case the (*****) becomes  *
        * a BEGIN_MULTI token with no following MULTI or NULL token.       *
        *******************************************************************/
      CToken.FindPfStepCTokens(tokens) ;
// INSERT here code to create PFLEVELNUM tokens in the array `tokens'
// Debug.print2DArray(tokens, "comtok");
        
      /*********************************************************************
      * Try to determine which of the tokens should be formated as         *
      * symbols.                                                           *
      *********************************************************************/
      if(tlaMode)
        { adjustIsTLA(tokens) ;
        } ;

      /*********************************************************************
      * Write out the comment.                                             *
      *********************************************************************/
      InnerWriteComment(writer, tokens, commentType, indentOrWidth);
    }

  
/* ------------------------ THE HASH TABLES ------------------------------ */

  public static void Initialize ()
    /***********************************************************************
    * Initializes the hash tables.                                         *
    ***********************************************************************/
    { ReadWordFile();
      InitializeAmbiguousHashtable();
      InitializeRepeatCharHashtable();
      InitializeAlignTokenHashtable();
    }


  private static String nullString = ""; 
    /***********************************************************************
    * Often, we want a hashtable that just keeps a bunch of keys, without  *
    * associating a value to the key.  But a Java hashtable entry needs a  *
    * value, which must be an object.  A string is an object, so a simple  *
    * null value is the empty string "".  However, if we just use "" as    *
    * the value, then Java creates a new object each time.  By using       *
    * nullString, there's just one object and lots of pointers to it.      *
    ***********************************************************************/
    

  /* ---------------------- THE word HASH TABLE ------------------------- */

  private static Hashtable wordHashTable  = new Hashtable(100000);
    /***********************************************************************
    * A hashtable of all common English words.                             *
    ***********************************************************************/

  public static boolean IsWord(String str) 
      /*********************************************************************
      * Returns true iff str is a common English word.                     *
      *********************************************************************/
      { return null !=  wordHashTable.get(str);
      } ;   

  private static void ReadWordFile()
    /***********************************************************************
    * Reads in the WordFile and puts its contents in wordHashTable.        *
    ***********************************************************************/
    { 
      ResourceFileReader wordFileReader
                     = new ResourceFileReader(Parameters.WordFile);

      String word = wordFileReader.getLine();
      while (word != null)
        { wordHashTable.put(word, nullString);
          wordHashTable.put(word.substring(0,1).toUpperCase() 
                                + word.substring(1), new String());
          word = wordFileReader.getLine() ;
        } ;
      wordFileReader.close();
    } ;


  /* -------------------- THE ambiguous HASH TABLE ---------------------- */

  private static Hashtable ambiguousHashTable  = new Hashtable(100);
    /***********************************************************************
    * A hashtable of all built-in symbols that can appear as ordinary      *
    * punctuation.  The entry for a symbol is the TeX string that          *
    * produces it.  (That string need work only outside math mode.)        *
    ***********************************************************************/

  public static boolean isAmbiguous(String str) 
    /***********************************************************************
    * Returns true iff str is a built-in symbol that can also appear as    *
    * ordinary punctuation.                                                *
    ***********************************************************************/
      { return null !=  ambiguousHashTable.get(str);
      } ;   

  private static String getAmbiguous(String str) 
    /***********************************************************************
    * Returns the true non-TLA TeX string for an ambiguous symbol.         *
    ***********************************************************************/
      { return (String) ambiguousHashTable.get(str);
      } ;   

  private static void add(String tla, String tex)
    /***********************************************************************
    * Adds an entry to the ambiguousHashTable.                             *
    ***********************************************************************/
    { ambiguousHashTable.put(tla, tex); } ;


  private static void InitializeAmbiguousHashtable()
    /***********************************************************************
    * Initializes the hash-table of ambiguous built-in symbols.            *
    ***********************************************************************/
    { add("_",    "\\_");
      add("(",    "(");
      add("[",    "[");
      add(")",    ")");
      add("]",    "]");
      add("~",    "\\ensuremath{\\sim}");
      add("'",    "\\mbox{'}");
      add("-",    "-");
      add("+",    "+");
      add("*",    "*");
      add("/",    "/");
      add("&",    "\\&");
      add("#",    "\\#");
      add(":",    ":");
      add("...",  "\\.{\\dots}");
      add("$",    "\\.{\\$}");
      add("?",    "\\.{?}");
      add("??",   "\\.{??}");
      add("%",    "\\.{\\%}");
      add("!!",   "\\.{!!}");
      add(",",    ",");
      add("!",    "!");
      add(".",    ".");
      add("@",    "@");
      add("--",   "--");
    } 

  /* -------------------- THE repeatChar HASH TABLE --------------------- */

  private static Hashtable repeatCharHashTable  = new Hashtable(100);
    /***********************************************************************
    * A hashtable of all characters that can be repeated to make some      *
    * sort of "dash", for example writing "==========".  We should define  *
    * a new object type for the entries.  However, to avoid the hassle,    *
    * we just let the entry be a Symbol object, where the fields have the  *
    * following meaning.                                                   *
    *                                                                      *
    *     TeXString  : A command \foo such that \foo{n} produces           *
    *                  the output for a string of n of the characters.     *
    *                  It equals "" if the TeXified characters themselves  *
    *                  should be used.                                     *
    *                                                                      *
    *     symbolType : The minimum number of characters needed             *
    *                  to qualify as a REP_CHAR CToken.                    *
    ***********************************************************************/

  public static boolean isRepeatChar(char ch) 
    /***********************************************************************
    * Returns true iff ch is a repeatable char.                            *
    ***********************************************************************/
      { return null !=  repeatCharHashTable.get("" + ch);
      } ;   

  private static String getRepeatCharCommand(char ch) 
    /***********************************************************************
    * Returns the command \foo such that \foo{n} produces the output for   *
    * a string of n ch characters, or "" if Misc.TeXify(the string of n    *
    * ch's) should be output.                                              *
    ***********************************************************************/
      { return ((Symbol) repeatCharHashTable.get("" + ch)).TeXString ;
      } ;   

  public static int getRepeatCharMin(char ch) 
    /***********************************************************************
    * Returns the minimum number of ch characters that constitutes a       *
    * REPEATED_CHAR CToken.                                                *
    ***********************************************************************/
      { return ((Symbol) repeatCharHashTable.get("" + ch)).symbolType ;
      } ;   

  private static void addRepeatChar(char ch, String tex, int min)
    /***********************************************************************
    * Adds an entry to the RepeatCharHashTable.                             *
    ***********************************************************************/
    { repeatCharHashTable.put("" + ch, 
                              new Symbol("", tex, min, 0));
    } ;

  private static void InitializeRepeatCharHashtable()
    { 
      addRepeatChar('-', "\\cdash", 3);
      addRepeatChar('=', "\\ceqdash", 3) ;
      addRepeatChar('^', "", 3) ;
      addRepeatChar('#', "", 3) ;
      addRepeatChar('_', "\\usdash", 2) ;
      addRepeatChar('~', "\\tdash", 2) ;
      addRepeatChar('*', "", 3) ;
      addRepeatChar('.', "", 4) ;
      addRepeatChar('+', "", 3) ;
    } ;


  /* -------------------- THE alignToken HASH TABLE --------------------- */

  private static Hashtable alignTokenHashTable  = new Hashtable(100);
    /***********************************************************************
    * A hashtable of all alignment tokens.  An alignment token t is one    *
    * such that, if two successive lines in a comment have t in the same   *
    * column, then those lines are considered to be aligned.  (Currently,  *
    * that alignment just causes the lines to begin separate paragraphs.)  *
    ***********************************************************************/

  private static boolean isAlignToken(String str)
    /***********************************************************************
    * Returns true iff str is (the string representation of) an alignment  *
    * comment token.                                                       *
    ***********************************************************************/
      { return null !=  alignTokenHashTable.get(str);
      } ;   

  private static void addAlignToken(String str)
    /***********************************************************************
    * Adds an entry to the alignTokenHashTable.                             *
    ***********************************************************************/
    { alignTokenHashTable.put(str, nullString);
    } ;

  private static void InitializeAlignTokenHashtable()
    /***********************************************************************
    * Sets the AlignToken hash table.  The idea is to consider a built-in  *
    * symbol to be an alignment token unless it seems likely that it will  *
    * lead to spurious alignments in ordinary text.                        *
    ***********************************************************************/
    {   addAlignToken("=>");
        addAlignToken("\\cdot");
        addAlignToken("<=>");
        addAlignToken("\\equiv");
        addAlignToken("~>");
        addAlignToken("-+->");
        addAlignToken("\\ll");
        addAlignToken("\\gg");
        addAlignToken("\\");
        addAlignToken("\\cap");
        addAlignToken("\\intersect");
        addAlignToken("\\cup");
        addAlignToken("\\union");
        addAlignToken("/\\");
        addAlignToken("\\/");
        addAlignToken("\\land");
        addAlignToken("\\lor");
        addAlignToken("\\X");
        addAlignToken("-");
        addAlignToken("+");
        addAlignToken("*");
        addAlignToken("^");
        addAlignToken("|");
        addAlignToken("||");
        addAlignToken("&");
        addAlignToken("&&");
        addAlignToken("++");
        addAlignToken("--");
        addAlignToken("**");
        addAlignToken("^^");
        addAlignToken("|-");
        addAlignToken("|=");
        addAlignToken("-|");
        addAlignToken("=|");
        addAlignToken("<:");
        addAlignToken(":>");
        addAlignToken(":=");
        addAlignToken("::=");
        addAlignToken("(+)");
        addAlignToken("(-)");
        addAlignToken("\\oplus");
        addAlignToken("\\ominus");
        addAlignToken("(.)");
        addAlignToken("\\odot");
        addAlignToken("(/)");
        addAlignToken("\\oslash");
        addAlignToken("(\\X)");
        addAlignToken("\\otimes");
        addAlignToken("\\uplus");
        addAlignToken("\\sqcap");
        addAlignToken("\\sqcup");
        addAlignToken("\\div");
        addAlignToken("\\star");
        addAlignToken("\\o");
        addAlignToken("\\circ");
        addAlignToken("\\bigcirc");
        addAlignToken("\\bullet");
        addAlignToken("\\in");
        addAlignToken("\\notin");
        addAlignToken("=");
        addAlignToken("#");
        addAlignToken("/=");
        addAlignToken("<");
        addAlignToken(">");
        addAlignToken("=<");
        addAlignToken(">=");
        addAlignToken("\\prec");
        addAlignToken("\\succ");
        addAlignToken("\\preceq");
        addAlignToken("\\succeq");
        addAlignToken("\\sim");
        addAlignToken("\\simeq");
        addAlignToken("\\approx");
        addAlignToken("\\doteq");
        addAlignToken("\\asymp");
        addAlignToken("\\sqsubset");
        addAlignToken("\\sqsupset");
        addAlignToken("\\sqsubseteq");
        addAlignToken("\\sqsupseteq");
        addAlignToken("\\propto");
        addAlignToken(":");
        addAlignToken("->");
        addAlignToken("|->");
        addAlignToken("<-");
        addAlignToken("==");
        addAlignToken("ELSE");
        addAlignToken("THEN");
        addAlignToken("LET");
        addAlignToken("IN");
        addAlignToken("[]");
        addAlignToken("..");
        addAlignToken("...");
        addAlignToken("$");
        addAlignToken("$$");
        addAlignToken("%");
        addAlignToken("%%");
        addAlignToken("##");
        addAlignToken("@@");
        addAlignToken("\\times");
        addAlignToken("\\leq");
        addAlignToken("\\geq");
        addAlignToken("\\mod");
        addAlignToken("\\wr");
        addAlignToken("\\cong");
        addAlignToken("-.");
        addAlignToken("@");

    } ;


/* ---------------------- MISCELLANEOUS METHODS ------------------------- */

  private static boolean 
      PossibleAlignment(CToken[][] com, int line, int itemNo)
    /***********************************************************************
    * True iff the token at com[line][item] is a candidate for an          *
    * word-alignment position.                                             *
    *                                                                      *
    *   Precondition: 0 < itemNo                                           *
    ***********************************************************************/
    { 
      return          (com[line][itemNo].column >
                         com[line][itemNo  - 1].column + 
                            com[line][itemNo - 1].getWidth() + 1)
                   || (   (com[line][itemNo].column >
                             com[line][itemNo - 1].column + 
                               com[line][itemNo - 1].getWidth())
                       && (com[line][itemNo - 1].type == CToken.BUILTIN)
                       && ! com[line][itemNo - 1].string.equals(".") 
                       && ! com[line][itemNo - 1].string.equals(",")) ;
    }

    
  private static CToken nextCToken(CToken[][] com, int line, int item)
    /***********************************************************************
    * The CToken following com[line][item].  However, if item is the last  *
    * one the line, then it equals a null Token (one with type NULL) if    *
    * the following line is blank, or the null value if this is the last   *
    * line.                                                                *
    ***********************************************************************/
    { if (item + 1 < com[line].length)
       { return com[line][item+1];
       }
      else
       { if (   (line + 1 < com.length)
             && (com[line + 1].length != 0)) 
           {return com[line + 1][0];}
       } ;
      return CToken.nullCToken ;
    }     


  private static CToken previousCToken(CToken[][] com, int line, int item)
    /***********************************************************************
    * The CToken preceding com[line][item].  However, if item is the       *
    * first one on the line, then it equals a null Token (one with type    *
    * NULL) if the previous line is blank, or the null value if this is    *
    * the first line.                                                      *
    ***********************************************************************/
    { if (item > 0)
       { return com[line][item - 1];
       }
      else
       { if (   (line > 0)
             && (com[line - 1].length != 0))
           {return com[line - 1][com[line - 1].length - 1];}
       } ;
      return CToken.nullCToken ;
    }     

  private static boolean isPreviousAdjacent(CToken[][] com, int line, int item)
    /***********************************************************************
    * True iff the token preceding the one at position (line, item) is     *
    * adjacent to the token at (line, item), with no intervening spaces.   *
    ***********************************************************************/
    { return    (item > 0)
             && (com[line][item-1].column + 
                   com[line][item-1].getWidth() == com[line][item].column) ;
    }
    

  

  private static boolean isNextAdjacent(CToken[][] com, int line, int item)
    /***********************************************************************
    * True iff the token following the one at position (line, item) is     *
    * adjacent to the token at (line, item), with no intervening spaces.   *
    ***********************************************************************/
    { return    (item + 1 < com[line].length)
             && (com[line][item].column + 
                   com[line][item].getWidth() == com[line][item+1].column) ;
    }
    


/* --------------------- THE adjustIsTLA METHODS ------------------------ */

  public static void adjustIsTLA(CToken[][] com)
    /***********************************************************************
    * Called after creating com with TokenizeComment.  That method sets    *
    * the isTLA field of tokens it determines to be TLA tokens (ones       *
    * typeset in math mode), and sets the isAmbiguous field of tokens      *
    * that might be TLA tokens.  The adjustIsTLA method decides which      *
    * ambiguous tokens should become TLA tokens.                           *
    ***********************************************************************/
    {int line = 0;
     int item = 0;
     CToken tok  = null ;
     CToken ptok = null ;
     CToken ntok = null ;
     /**********************************************************************
     * Check for the following special cases.                              *
     *  - a "'" token is immediately followed by an IDENT.                 *
     *  - a "-" token is either:                                           *
     *     * Ends the line and is immediately preceded by an IDENT id1     *
     *     * Is immediately preceded by an IDENT and immediately           *
     *       followed by an IDENT that are not both TLA tokenS.            *
     * - a "+" token immediately following "TLA".                          *
     **********************************************************************/
     line = 0 ;
     while (line < com.length)
      {item = 0 ;
       while (item < com[line].length)
        {tok = com[line][item];
         if (!tok.isTLA)
          { ptok = previousCToken(com, line, item) ;
            ntok = nextCToken(com, line, item) ;

            if(tok.string.equals("'"))
             { if (   (isNextAdjacent(com, line, item))
                   && (ntok.type == CToken.IDENT))
                 { tok.isAmbiguous = false ;
                   ntok.isAmbiguous = false ;
                   ntok.isTLA = false ; 
                 };
             } ;

            if(tok.string.equals("-"))
             { if(isPreviousAdjacent(com, line, item))
                { if (   (item == com[line].length - 1)
                      && (ptok.type == CToken.IDENT)
                      && (! ptok.isTLA) )
                    { tok.isAmbiguous = false ;
                      ptok.isAmbiguous = false ;
                    };
                  
                  if (   (isNextAdjacent(com, line, item))
                      && (ntok.type == CToken.IDENT)
                      && (  (! ntok.isTLA) 
                          ||(! ptok.isTLA) ))
                    { tok.isAmbiguous = false ;
                      ptok.isAmbiguous = false ;
                      ntok.isAmbiguous = false ;
                    };
                } 
             }

            if(   (tok.string.equals("+"))
               && isPreviousAdjacent(com, line, item)
               && ptok.string.equals("TLA"))
             { tok.isAmbiguous = false ;
               ptok.isAmbiguous = false ;
             };
           };
         item = item + 1;
        };                   // END while (item < ...)
       line = line + 1;
      } ;                    // END while (line < ...)


     /**********************************************************************
     * Set the isTLA field true in the following cases:                    *
     *                                                                     *
     *  - If an IDENT immediately follows a "." (with no space),           *
     *    set true for Ident and ".".  If the "." is also                  *
     *    immediately preceded by a token (with no intervening space),     *
     *    set true for that token too.                                     *
     *                                                                     *
     *  - If a "(" or "[" immediately follows a token (with no space),     *
     *    set true for it and the preceding token.                         *
     **********************************************************************/
     line = 0 ;
     while (line < com.length)
      {item = 0 ;
       while (item < com[line].length)
        {
         tok  = com[line][item] ;
         if(   (tok.string.equals("."))
            && isNextAdjacent(com, line, item)
            && (com[line][item + 1].type == CToken.IDENT))
           { tok.isTLA  = true ;
             com[line][item + 1].isTLA = true ;
             if (isPreviousAdjacent(com, line, item))
               { com[line][item - 1].isTLA = true ;
               }
           }
         else
           { if (   (   (tok.string.equals("("))
                     || (tok.string.equals("[")))
                 && isPreviousAdjacent(com, line, item))
              { tok.isTLA = true ;
                com[line][item - 1].isTLA = true ;
              }
           } ;
         item = item + 1;
        }
       line = line + 1;
      } ;    // END while


     /**********************************************************************
     * Set the isTLA field for any ambiguous IDENT that is NOT either      *
     *                                                                     *
     *     (i) All lower-case or                                           *
     *                                                                     *
     *    (ii) All-upper case whose lower-case form is in the dictionary.  *
     *                                                                     *
     *   (iii) All letters with the first letter capitalized that either   *
     *           (a) follows a ".", "(", ")", double-quote, or two or      *
     *               more spaces, or                                       *
     *           (b) is the first token of the line.                       *
     **********************************************************************/
     line = 0 ;
     while (line < com.length)
      {item = 0 ;
       while (item < com[line].length)
        { tok = com[line][item] ;
          ptok = previousCToken(com, line, item);
          String tstr = tok.string;
          if (   (tok.type == CToken.IDENT)
              && tok.isAmbiguous
              && ! (   Misc.IsLowerCase(tstr)
                    || (   Misc.IsUpperCase(tstr)
                        && IsWord(tstr.toLowerCase()))
                    || (   Misc.IsCapitalized(tstr)
                        && (   (item == 0)
                            || ptok.string.equals(".")
                            || ptok.string.equals("(")
                            || ptok.string.equals(")")
                            || (ptok.type == CToken.RIGHT_DQUOTE)
                            || (ptok.type == CToken.LEFT_DQUOTE)
                            || (ptok.column + ptok.getWidth() 
                                  <= tok.column - 2 )))))
            { tok.isTLA = true; }
            
         item = item + 1;
        }
       line = line + 1;
      } ;    // END while

     /**********************************************************************
     * We now catch anomalies like "CONSTANT DECLARATIONS", to turn the    *
     * "CONSTANT" from a BUILTIN token to an IDENT. We do this if the      *
     * BUILTIN is an upper-case word and is adjacent to an upper-case      *
     * IDENT.                                                              *
     **********************************************************************/
     line = 0 ;
     while (line < com.length)
      {item = 0 ;     
       while (item < com[line].length)
        { tok = com[line][item] ;
          if (   (tok.type == CToken.BUILTIN)
              && Misc.IsUpperCase(tok.string)
              && (   (   (item > 0)
                      && (com[line][item-1].type == CToken.IDENT)
                      && ! com[line][item-1].isTLA
                      && Misc.IsUpperCase(com[line][item-1].string))
                  || (   (item + 1 < com[line].length)
                      && (com[line][item+1].type == CToken.IDENT)
                      && ! com[line][item+1].isTLA
                      && Misc.IsUpperCase(com[line][item+1].string))))
            { tok.type = CToken.IDENT;
              tok.isTLA = false;
            } ;
  
          item = item + 1;
        }
       line = line + 1;
      } ;      
       
     /**********************************************************************
     * For each built-in symbol of type LEFT_PAREN whose isTLA field is    *
     * true, set the isTLA field true of every token through the next      *
     * matching RIGHT_PAREN, "]_", or next blank line.                     *
     **********************************************************************/
     int parenLevel = 0 ;
       /********************************************************************
       * The number of levels deep within a LEFT_PAREN token with isTLA =  *
       * true.                                                             *
       ********************************************************************/
     line = 0 ;
     while (line < com.length)
      {item = 0 ;
       if (com.length == 0) 
        { parenLevel = 0 ; } ;
       while (item < com[line].length)
        {
         tok  = com[line][item] ;
         if (parenLevel > 0)
          { tok.isTLA = true; } ;

         if (   (tok.type == CToken.BUILTIN)
             && (BuiltInSymbols.GetBuiltInSymbol(tok.string, true).symbolType
                   == Symbol.LEFT_PAREN)
             && (   (parenLevel > 0)
                 || tok.isTLA))
          { parenLevel = parenLevel + 1; }

         else
          { if (   (tok.type == CToken.BUILTIN)
                && (  (BuiltInSymbols.GetBuiltInSymbol(tok.string, true).symbolType
                         == Symbol.RIGHT_PAREN)
                    || tok.string.equals("]_"))
                && (parenLevel > 0) )
             { parenLevel = parenLevel - 1; };
          };
         item = item + 1;
        }

       line = line + 1;
      }     

     /**********************************************************************
     * Try to resolve ambiguous tokens based on what's next to them,       *
     * using the following rules:                                          *
     *                                                                     *
     *  - Set isTLA true for an ambiguous IDENT if it is preceded by       *
     *    an INFIX or PREFIX operator or is followed by a POSTFIX          *
     *    operator--or if the -tlaComment option is chosen.                *
     *                                                                     *
     *  - Set isTLA true for an ambiguous INFIX operator if it is          *
     *    preceded or followed by an isTLA or ambiguous token.             *
     *                                                                     *
     *  - Set isTLA true for an ambiguous PREFIX/POSTFIX operator          *
     *    if it is followed/preceded by an isTLA or ambiguous token.       *
     **********************************************************************/
     line = 0 ;
     while (line < com.length)
      {item = 0 ;
       while (item < com[line].length)
        {tok  = com[line][item] ;
         ptok = previousCToken(com, line, item);
         ntok = nextCToken(com, line, item);
         if ( (! tok.isTLA) && tok.isAmbiguous)
          { switch (tok.type)
             {case CToken.IDENT  :
              case CToken.NUMBER :
                if (Parameters.TLACommentOption)
                 { tok.isTLA = true ;
                 }
                else
                 {
                   if (ptok.type == CToken.BUILTIN)
                    {int stype = 
                      BuiltInSymbols.GetBuiltInSymbol(ptok.string, true).symbolType;
                      if (   (   (stype == Symbol.INFIX)
                              || (stype == Symbol.PREFIX))
                          && ( ptok.isTLA || ptok.isAmbiguous))
                       { tok.isTLA = true ;
                         ptok.isTLA = true ;
                       }
                    } ;
                  } ;
                if (ntok.type == CToken.BUILTIN)
                 {int stype = 
                   BuiltInSymbols.GetBuiltInSymbol(ntok.string, true).symbolType;
                   if (   (   (stype == Symbol.INFIX)
                           || (stype == Symbol.POSTFIX))
                       && ( ntok.isTLA || ntok.isAmbiguous))
                    { tok.isTLA = true ;
                      ntok.isTLA = true ;
                    }
                 } ;
                break;
              case CToken.BUILTIN  :
                int stype = 
                     BuiltInSymbols.GetBuiltInSymbol(tok.string, true).symbolType;
                if (   (   (stype == Symbol.PREFIX)
                        || (stype == Symbol.INFIX) )
                    && ( ntok.isTLA || ntok.isAmbiguous))
                 { tok.isTLA = true ;
                   ntok.isTLA = true ;
                 } ;
                if (   (   (stype == Symbol.INFIX) 
                        || (stype == Symbol.POSTFIX))
                    && ( ptok.isTLA || ptok.isAmbiguous))
                 { tok.isTLA = true ;
                   ptok.isTLA = true ;
                 } ;
                break;
              default :
                Debug.ReportBug("FormatComments.adjustIsTLA: "
                  + "ambiguous CToken of wrong type");
             }
          }
         item = item + 1;
        }

       line = line + 1;
      }     

     /**********************************************************************
     * For each ambiguous IDENT token, set it to be a TLA token if it      *
     * occurs anywhere in the comment as a TLA token and is not a word.    *
     **********************************************************************/
     
     /**********************************************************************
     * Set thisCommentTLA to be a hash table of all TLA IDENT tokens.      *
     **********************************************************************/
     Hashtable thisCommentTLA  = new Hashtable(100);     
     line = 0 ;
     while (line < com.length)
      {item = 0 ;
       while (item < com[line].length)
        {tok = com[line][item];
         if (   (tok.type == CToken.IDENT)
             && tok.isTLA)
          { thisCommentTLA.put(tok.string, nullString);
          }
         item = item + 1;
        }
       line = line + 1;
      }  

     /**********************************************************************
     * Set all the ambiguous IDENTs that are in thisCommentTLA to TLA      *
     * tokens..                                                            *
     **********************************************************************/
     line = 0 ;
     while (line < com.length)
      {item = 0 ;
       while (item < com[line].length)
        { tok = com[line][item];
          if (   (tok.isAmbiguous)
              && (! IsWord(tok.string))
              && null != thisCommentTLA.get(tok.string))
            { tok.isTLA = true; }
          item = item + 1;
        }
       line = line + 1;
      }  

     /**********************************************************************
     * We now set the isTLA field false for any VERB and TEX token.  (The  *
     * field can get set for these tokens by bizarre inputs, and it's      *
     * easier to just reset them here than worry about it in the code      *
     * above.)                                                             *
     **********************************************************************/
     line = 0 ;
     while (line < com.length)
      {item = 0 ;
       while (item < com[line].length)
        { tok = com[line][item];
          if (   (tok.type == CToken.VERB)
              || (tok.type == CToken.TEX))
            { tok.isTLA = false; }
          item = item + 1;
        }
       line = line + 1;
      }  

    }                       // END public static void adjustIsTLA


/* ------------------- THE InnerWriteComment METHOD --------------------- */

  private static boolean IsTLALine(CToken[] tokLine)
    /***********************************************************************
    * Returns true iff every token in tokLine is a TLA token.              *
    ***********************************************************************/
    { boolean result = true ;
      int i = 0;
      while ( result && (i < tokLine.length))
        { result = tokLine[i].isTLA ;
          i = i + 1;
        } ;
      return result ;
    } 
    
  private static void InnerWriteComment(OutputFileWriter writer, 
                                        CToken[][]       com, 
                                        int              commentType,
                                        float            indentOrWidth)
   /************************************************************************
   * This does the actual writing of the output for the WriteComment       *
   * method.                                                               *
   ************************************************************************/
   { // BEGIN InnerWriteComment(...)

  /*************************************************************************
  * PARAGRAPH SHAPING                                                      *
  *                                                                        *
  * Paragraph shaping is defined by the following rules, where the         *
  * prevailing (left) margin is initially the left-most column occupied by *
  * a token.  The EDGE of a line is the column of its left-most token.     *
  *                                                                        *
  * Two paragraphs need not have a blank line between them.  If they       *
  * don't, then there is no vertical space between them.                   *
  *                                                                        *
  * If line i begins a paragraph, then it is a one-line paragraph if it    *
  * consists entirely of TLA tokens, it is aligned in some way with the    *
  * following line, or the following line is indented less than it is.     *
  * Otherwise, its paragraph ends with either the first blank line, or     *
  * the first line whose left edge is different from the left edge of the  *
  * paragraph's SECOND line.                                               *
  *                                                                        *
  * The prevailing margin at the start of a paragraph is the most recent   *
  * prevailing margin that is at or to the left of the left-most edge of   *
  * the lines of the paragraph.  For example, if the prevailing margin     *
  * after each paragraph iiiiii is at its left edge, then the prevailing   *
  * margin at the start of 3333 in                                         *
  *     1111                                                               *
  *        2222                                                            *
  *       3333                                                             *
  * is the edge of 1111.                                                   *
  *                                                                        *
  * The prevailing margin after the paragraph is the edge of the           *
  * paragraph's SECOND line--or its first if it only has one line.  (Hence *
  * the new prevailing margin is always \geq the old prevailing margin.)   *
  *                                                                        *
  * The shape of the paragraph is determined according to these two        *
  * cases, where d is the distance between the new and old prevailing      *
  * left margins.                                                          *
  *                                                                        *
  * - Edge of line 1 = Edge of line 2:                                     *
  *      old margin ->|    111111                                          *
  *                        222222                                          *
  *           new margin ->|                                               *
  *                                                                        *
  * d is determined by number of columns between old margin and line 1.    *
  * A single-line paragraph is also shaped in this way.                    *
  *                                                                        *
  * - Edge of line 1 to left of Edge of line 2:                            *
  *   If the edge of line 2 aligns with the beginning of a                 *
  *   token in line 1, then this is a labeled paragraph                    *
  *                                                                        *
  *      old margin ->|    111 111                                         *
  *                            222222                                      *
  *               new margin ->|                                           *
  *                                                                        *
  *   where line 2 is aligned with the token, and the space to the         *
  *   left of the label and between the label and the rest of line 1       *
  *   is determined by the number of spaces in the input.  Otherwise,      *
  *                                                                        *
  *      old margin ->|    111111                                          *
  *                            222222                                      *
  *               new margin ->|                                           *
  *                                                                        *
  *   Where the indentations of line 1 and of line 2 are determined by     *
  *   the number of columns of indentation in the input.                   *
  *                                                                        *
  *************************************************************************/
    int[] lineType    = new int[com.length];
    String[] parStart = new String [com.length];
      /*********************************************************************
      * These arrays determine the paragraph shape of the comment.  The    *
      * value of lineType[i] has the following meaning:                    *
      *                                                                    *
      *    -2 : A blank line.                                              *
      *                                                                    *
      *    -1 : A non-blank line that does not begin a paragraph.          *
      *                                                                    *
      *     0 : A non-blank line that begins an unlabeled paragraph        *
      *                                                                    *
      *   > 0 : A non-blank line that begins a labeled paragraph.  In this *
      *         case, the first lineType[i] tokens of the line form        *
      *         the paragraph's label.                                     *
      *                                                                    *
      * If lineType[i] = 0, then parStart[i] is the "\begin{...}" command  *
      * that begins the paragraph.  If lineType[i] > 0, it's the command   *
      * "\begin...{", which must then be followed by the label and the     *
      * closing "}"                                                        *
      *                                                                    *
      * For a one-line comment, they are arrays of length 1 with           *
      * lineType[0] = -1                                                   *
      *                                                                    *
      * Invariant :                                                        *
      *    (lineType[i] > 0) => (lineType[i] + 1 < com[i].length)          *
      *                                                                    *
      * In other words, there are always more than lineType[i] tokens      *
      * on a non-blank line.                                               *
      *********************************************************************/

      /*********************************************************************
      * We first set oneLine[i] to be true iff line i is a one-line        *
      * paragraph.  This is the case if either:                            *
      *                                                                    *
      *  1. It is a line of all TLA tokens.                                *
      *                                                                    *
      *  2. There is an alignment or REP_CHAR token tok in this            *
      *     line aligned with an identical token in the next line,         *
      *     where tok is not immediately adjacent to the tokens on         *
      *     both sides.  Moreover, in this case, the following line is     *
      *     also a one-line par if the line after it is outdented from     *
      *     it.  In this case, we also mark the following line as a        *
      *     one-line paragraph if it ends the paragraph--that is, if it    *
      *     is followed by a blank line or ends the comment.               *
      *********************************************************************/
      boolean[] oneLine = new boolean[com.length] ;

      boolean thisAligned = false ;
      boolean prevAligned = false;
        /*******************************************************************
        * True iff this or the previous line was aligned (case 2).         *
        *******************************************************************/
      int line = 0 ;
      while (line < com.length)
       { thisAligned = false ;
         if (   (line + 1 < com.length)
             && (com[line+1].length != 0) )
          { int m = 0 ;
            int n = 0 ;
            int lastn = com[line+1].length ;
            while (   !thisAligned
                   && (m < com[line].length)
                   && (com[line][m].column <= com[line+1][lastn-1].column))
             {CToken mtok = com[line][m] ;
              if (   (   isAlignToken(mtok.string)
                      || (mtok.type == CToken.REP_CHAR))
                  && ! (   isPreviousAdjacent(com, line, m)
                        && isNextAdjacent(com, line, m)))
               {while (   !thisAligned
                       && (n < lastn)
                       && (mtok.column >= com[line+1][n].column))
                {CToken ntok = com[line+1][n] ;
                 if (   (mtok.column == ntok.column)
                     && (mtok.string.equals(ntok.string))
                     && ! (   isPreviousAdjacent(com, line+1, n)
                           && isNextAdjacent(com, line+1, n)))
                  { thisAligned = true;
                  } ;
                 n = n+1 ;
                } ;              
               }
               m = m + 1;
             }
           };
         oneLine[line] =    thisAligned 
                         || IsTLALine(com[line])
                         || (   prevAligned
                             && (line + 1 < com.length)
                             && (com[line + 1].length > 0)
                             && (com[line][0].column 
                                    > com[line + 1][0].column)) ;
         if (   (thisAligned)
             && (   (line + 2 == com.length)
                 || (com[line + 2].length == 0)))
          { oneLine[line + 1] = true ; } ;

         prevAligned = thisAligned ;
         line = line + 1;
       } ;

    /***********************************************************************
    * Now we look for successive lines that begin with the same token.     *
    * If there are n successive lines beginning with the same token that   *
    * is not a short (fewer than 4-character) or unambiguous lower-case    *
    * word we make the first n-1 of them one-line paragraphs.  If the      *
    * n-th is the end of a paragraph, we make it a one-line paragraph      *
    * too.                                                                 *
    ***********************************************************************/
    line = 0;
    while (line + 1 < com.length)    
     { if (com[line].length != 0)
         { CToken tok = com[line][0] ;
           if (   (com[line+1].length != 0)
               && tok.string.equals(com[line+1][0].string)
               && (   (tok.type != CToken.IDENT)
                   || (  (tok.string.length() >= 4)
                       && tok.isAmbiguous)
                   || tok.isTLA )
               && (tok.isTLA == com[line+1][0].isTLA))
                    /*******************************************************
                    * We might get lucky and avoid a chance alignment      *
                    * with this condition.                                 *
                    *******************************************************/
             { oneLine[line] = true ;
               if (   (line + 2 == com.length)
                   || (com[line + 2].length == 0))
                 { oneLine[line + 1] = true ; }
             } ;
         };
       line = line + 1;
     } ;

    /***********************************************************************
    * Now we look for successive lines that begin with a number.  If       *
    * there are n successive lines beginning with a number, we make the    *
    * first n-1 of them one-line paragraphs.  If the n-th is the end of a  *
    * paragraph, we make it a one-line paragraph too.                      *
    ***********************************************************************/
    line = 0;
    while (line + 1 < com.length)    
     { if (   (com[line].length != 0)
           && (com[line][0].type == CToken.NUMBER)
           && (com[line+1].length != 0)
           && (com[line+1][0].type == CToken.NUMBER))
         { oneLine[line] = true ;
           if (   (line + 2 == com.length)
               || (com[line + 2].length == 0))
             { oneLine[line + 1] = true ; }
         };
       line = line + 1;
     } ;


    /***********************************************************************
    * We next look for alignments of arbitrary words that suggest some     *
    * sort of table--for example                                           *
    *                                                                      *
    *      foo:    XXX                                                     *
    *      grunch: XXX                                                     *
    *      a:      XXX                                                     *
    *                                                                      *
    * We regard this as an alignment if there are at least three           *
    * successive aligned lines, the aligned tokens have the same item      *
    * number, which is betweem 1 and 5, and each token has either two or   *
    * more spaces to its left, or one space and a built-in token to its    *
    * left that is not "." or ",".  (This should make chance alignments    *
    * unlikely.)                                                           *
    *                                                                      *
    * Note that this would be a fine opportunity to use tabular            *
    * alignment, but we won't do that unless it seems worth doing.         *
    * Instead, we just mark the first n-1 as single-paragraph lines, and   *
    * the n-th as well if it ends a paragraph.                             *
    *                                                                      *
    * Note: requiring that the aligned tokens all have the same item       *
    * number may be too strong.  However, I think I've reached the point   *
    * of diminishing returns in this kind of tinkering.  If we want to do  *
    * better, we need to re-design the whole paragraph shaping algorithm.  *
    ***********************************************************************/
    line = 0;
    while (line < com.length)    
     { int itemNo = 1 ;
       int maxUnalignedLine = line + 1;
       while (    (itemNo <= 5)
               && (itemNo < com[line].length))
        { 
          if (PossibleAlignment(com, line, itemNo))
           { int col = com[line][itemNo].column ;
             int nextLine = line + 1 ;
             while (   (nextLine < com.length)
                    && (itemNo < com[nextLine].length)
                    && PossibleAlignment(com, nextLine, itemNo)
                    && (com[nextLine][itemNo].column == col))
              { nextLine = nextLine + 1;}
             if (nextLine > maxUnalignedLine)
               {maxUnalignedLine = nextLine ;}
           } ;
          itemNo = itemNo + 1;
        }
       if (maxUnalignedLine - line >= 3)
         { int kk = line;
           while (kk < maxUnalignedLine - 1)
            { oneLine[kk] = true ;
              kk = kk + 1;
            }
          if (    (maxUnalignedLine == com.length)
               || (com[maxUnalignedLine].length == 0))
             { oneLine[maxUnalignedLine - 1] = true ; }
         };
       line = line + 1;
     } ;

    /***********************************************************************
    * We also turn any line consisting only of REP_CHAR tokens into a      *
    * one-line paragraph.                                                  *
    ***********************************************************************/
    line = 0;
    while (line < com.length)    
     { if (com[line].length != 0)
         { int item = 0 ;
           while (   (item < com[line].length)
                  && (com[line][item].type == CToken.REP_CHAR))
             { item = item + 1; } 
           if (item == com[line].length)
             { oneLine[line] = true ; } 
         }
       line = line + 1;
     } ;
      
    
    /***********************************************************************
    * Compute lineType and parStart.                                       *
    ***********************************************************************/
    int marginDepth = 0 ;
      /*********************************************************************
      * The depth of the current prevailing margin.                        *
      *********************************************************************/
    int[] margin = new int[200] ;
      /*********************************************************************
      * for 0 \leq i \leq parDepth, margin[i] is the depth i prevailing    *
      * left margin (a column number)                                      *
      *********************************************************************/

    /***********************************************************************
    * Set margin[0] to left-most token column.                             *
    ***********************************************************************/
    line = 0 ;
    margin[0] = 999;
    while (line < com.length)
      { if (   (com[line].length > 0)
            && (com[line][0].column < margin[0]))
          {margin[0] = com[line][0].column ;}
        line = line + 1;
      };

    /***********************************************************************
    * startNewPar is true if the next non-blank line starts a new          *
    * paragraph.                                                           *
    ***********************************************************************/
    boolean startNewPar = false ;
    if (IsParType(commentType))
     {                           // BEGIN then OF if (IsParType(commentType))
      startNewPar = true ; 
      line = 0 ;
      while (line < com.length)
       {                // BEGIN while (line < com.length)
        if (com[line].length == 0)
         { lineType[line] = -2 ; 
           line = line + 1;
         }
        else
         {                // BEGIN else of if (com[line].length == 0)
          /***************************************************************
          * A new paragraph starts at this line.                         *
          ***************************************************************/
          int nextParLine = line + 1;
            /**************************************************************
            * The line after the end of this paragraph                    *
            **************************************************************/
          int newMargin = com[line][0].column ;
            /**************************************************************
            * The new prevailing margin.                                  *
            **************************************************************/
          int labelItem = 0 ;
            /**************************************************************
            * The number of the item on this line with which the next     *
            * line is aligned, if this is a labeled paragraph; otherwise  *
            * zero.                                                       *
            **************************************************************/
          int popArg = 0 ;
          boolean nest  = false ;
          String nestArg  = "F" ;
          boolean isLabel = false ;
          String isLabelArg  = "F" ;
          int dim1Cols = 0 ;
          int dim2Cols = 0 ;
            /**************************************************************
            * The arguments or values that determine the arguments of     *
            * the LaTeXCommentPar environment.                            *
            **************************************************************/
          if (   (com[line][0].type == CToken.VERB)
              || (   (com[line][0].type == CToken.TEX) )
                  && (com[line].length == 1))
           {    // BEGIN then OF if ((com[line][0].type == CToken.VERB)...)
            /***************************************************************
            * This is a VERB or TEX line.                                  *
            *                                                              *
            * A VERB line is one that begins with a VERB token.  A VERB    *
            * token that does not appear at the beginning of a line will   *
            * be TeXify'ed and typeset as is.  A sequence of VERB lines    *
            * is typeset verbatim, with the prevailing margin reset to     *
            * the left edge.                                               *
            *                                                              *
            * A TEX line is one consisting of a single TEX token.  A TEX   *
            * token that doesn't form a TEX line will be typeset in situ   *
            * as TeX input.  A sequence of lines beginning with a TEX      *
            * line and followed by lines beginning with a TEX token is     *
            * typeset in a new paragraph, whose left margin is determined  *
            * by the column of the "`^" token.  (If the "`^" token         *
            * appeared on a previous line, then we act as if the "`^"      *
            * appeared in column 0.)                                       *
            ***************************************************************/
            int tokType = com[line][0].type ;            
             
            if (tokType == CToken.VERB)
              /*************************************************************
              * For a sequence of VERB lines, the margin is reset to the   *
              * left edge.                                                 *
              *************************************************************/
              { newMargin = 0 ;
                popArg = marginDepth ;
                marginDepth = 0 ;
              }
            else
              /*************************************************************
              * For a sequence of TEX lines, the margin is determined by   *
              * the column of the first token.                             *
              *************************************************************/
              { /***********************************************************
                * Set newMargin to the first token's column, set           *
                * marginDepth to the depth of the prevailing margin for    *
                * this paragraph, and set popArg.                          *
                ***********************************************************/
                newMargin = com[line][0].column ;

                while (margin[marginDepth] > newMargin)
                 { marginDepth = marginDepth - 1;
                   popArg = popArg + 1;
                 }
                /***********************************************************
                * Set dim1Cols to number of columns from the prevailing    *
                * margin to newMargin of first line.                       *
                ***********************************************************/
                dim1Cols = com[line][0].column - margin[marginDepth];
            
              } ;
            /***************************************************************
            * All immediately following VERB/TEX lines get lineType = -1.  *
            ***************************************************************/
            while (   (nextParLine < com.length)
                   && (com[nextParLine].length > 0)
                   && (com[nextParLine][0].type == tokType))
             { nextParLine = nextParLine + 1; } ;
           }      // END then OF ((com[line][0].type == CToken.VERB)...)
          else
           {     // BEGIN else OF if ((com[line][0].type == CToken.VERB)...)


            if (   (! oneLine[line])
                && (line + 1 < com.length)
                && (com[line + 1].length != 0)
                && ! oneLine[line + 1] 
                && (com[line + 1][0].column >= com[line][0].column))
                   /********************************************************
                   * This is a one-line paragraph if the following line    *
                   * is outdented from this one.                           *
                   ********************************************************/
              { /***********************************************************
                * This paragraph has at least two lines.                   *
                ***********************************************************/
                newMargin = com[line + 1][0].column ;
                nextParLine = line + 2 ;
                
                /***********************************************************
                * Add new lines to the paragraph as long as they are       *
                * aligned with the second line.                            *
                ***********************************************************/
                while (   (nextParLine < com.length)
                       && (com[nextParLine].length != 0)
                       && ! oneLine[nextParLine]
                       && (com[nextParLine][0].column == newMargin))
                 { nextParLine = nextParLine + 1; } ;
              };           
  
            /***************************************************************
            * Set leftMargin to the left margin of the paragraph, which    *
            * is the leftmost of the first two lines.                      *
            ***************************************************************/
            int leftMargin = com[line][0].column;
            if (leftMargin > newMargin )
              { leftMargin = newMargin; }
            /****************************************************************
            * Set marginDepth to the depth of the prevailing margin for     *
            * this paragraph, and set popArg.                               *
            ****************************************************************/
            while (margin[marginDepth] > leftMargin)
              { marginDepth = marginDepth - 1;
                popArg = popArg + 1;
              }
  
            /****************************************************************
            * Set dim1Cols to number of columns from the prevailing margin  *
            * to newMargin of first line.                                   *
            ****************************************************************/
            dim1Cols = com[line][0].column - margin[marginDepth];
  
            /****************************************************************
            * Set nest and nestArg.                                         *
            ****************************************************************/
            nest = (margin[marginDepth] != newMargin);
            if (nest) {nestArg = "T";};
  
            /****************************************************************
            * Determine if this is a labeled paragraph.                     *
            ****************************************************************/
            if (com[line][0].column < newMargin)
              { int i = 0 ;
                while (   (i+1 < com[line].length)
                       && (com[line][i+1].column <= newMargin))
                 {i = i+1;};
                isLabel = (com[line][i].column == newMargin) ;
                if (isLabel) {labelItem = i;
                              isLabelArg = "T";
                             };
              };
  
            /*****************************************************************
            * Determine dim2Cols.                                            *
            *****************************************************************/
            if (isLabel)
              { dim2Cols = com[line][labelItem].column 
                              - com[line][labelItem - 1].column 
                              - com[line][labelItem - 1].getWidth();
              }
            else
              { dim2Cols = newMargin - com[line][0].column;
              } ;
  
            /*****************************************************************
            * Update marginDepth and margin, if necessary.                   *
            *****************************************************************/
            if (nest){ marginDepth = marginDepth + 1;
                       margin[marginDepth] = newMargin ;
                     } ;
           };    // END else OF if ((com[line][0].type == CToken.VERB)...)
  
          /*****************************************************************
          * Set lineType[line] and parStart[line].                         *
          *****************************************************************/
          lineType[line] = labelItem ;
          String temp =    
             "\\begin{" + Parameters.LaTeXCommentPar 
            + "}{" + popArg + "}{" + nestArg + "}{" + isLabelArg + "}{"
            + Misc.floatToString(Parameters.LaTeXCommentLeftSpace(dim1Cols),2)
            + "}{"
            + Misc.floatToString(Parameters.LaTeXCommentLeftSpace(dim2Cols),2)
            +"}{" ;
          if (isLabel)
           { parStart[line] = temp + "%"; }
          else
           { parStart[line] = temp + "}%"; };
            
          /*****************************************************************
          * Set lineType for the rest of the lines of the paragraph, and   *
          * set line to nextParLine.                                       *
          *****************************************************************/
          line = line + 1;
          while (line < nextParLine)
           { lineType[line] = -1 ;
             line = line + 1;
           } ;
        };                    // END else OF if (com[line].length == 0);
      }                      // END while (line < com.length)
     }                          // END then OF if (IsParType(commentType))
    else
     {                           // BEGIN else OF if (IsParType(commentType))
      if (com.length != 0)
        { lineType[0]   = -1;
        } ;
     }                           // END else OF if (IsParType(commentType))


    line = 0;
    /***********************************************************************
    * Set line to the first non-null line (or com.length if there is       *
    * none).                                                               *
    ***********************************************************************/
    while (   (line < com.length)
           && (lineType[line] == -2))
     { line = line + 1;
     };

    /***********************************************************************
    * Set endLine to the line after the last non-null line, or to (or to   *
    * com.length if there is none).                                        *
    ***********************************************************************/
    int endLine = com.length ;
      /*********************************************************************
      * The line after the last non-null line.                             *
      *********************************************************************/
    while (   (endLine > line)
           && (lineType[endLine - 1] == -2))
     { endLine = endLine - 1;
     };

    if (   (line == endLine)
        || (   !IsParType(commentType)
            && (com[0].length == 0)))
     /**********************************************************************
     * This is the null comment.  We write nothing except for commentType  *
     * ONE_LINE, in which case we write a null comment.                    *
     **********************************************************************/
     { if (commentType == ONE_LINE)
         { writer.putLine(Parameters.LaTeXOneLineCommentCommand + "{}%");};
       return ;
     }     

    /***********************************************************************
    * Write out the opening of the comment.                                *
    ***********************************************************************/
    String tempStr = "";
    switch (commentType)
      {
       case ONE_LINE :
         tempStr = Parameters.LaTeXOneLineCommentCommand + "{" ;
         if (   (com[0].length > 0)
             && (com[0][0].column > 0))
           { tempStr = tempStr + 
                  Parameters.LaTeXSpaceCommand + "{" 
                + Misc.floatToString(Parameters.LaTeXCommentLeftSpace(
                   com[0][0].column - 1), 2)
                + "}" ;
           } ;
         writer.putLine(tempStr + "%");
         break ;

       case ZERO_WIDTH :
         tempStr = Parameters.LaTeXZeroWidthCommentCommand + "{" ;
         if (   (com[0].length > 0)
             && (com[0][0].column > 0))
           { tempStr = tempStr + 
                  Parameters.LaTeXSpaceCommand + "{" 
                + Misc.floatToString(Parameters.LaTeXCommentLeftSpace(
                   com[0][0].column - 1), 2)
                + "}" ;
           } ;
         writer.putLine(tempStr + "%");
         break ;

       case PAR :
         float indent = indentOrWidth ;

         if (indent < -1)
           { indent = Parameters.LaTeXCommentLeftSpace(margin[0]);
           } ;
         writer.putLine("\\begin{" 
                             + Parameters.LaTeXLeftMultiLineComment
                             + "}{" + Misc.floatToString(indent,2) 
                             + "}%");
         break ;

       case RIGHT_MULTI :
         writer.putLine("\\begin{" 
                             + Parameters.LaTeXRightMultiLineComment
                             + "}{" + Misc.floatToString(indentOrWidth,2) 
                             + "}%");
         break ;
       default :
         Debug.ReportBug(
           "The impossible has happened in FormatComments.InnerWriteComment");
      }

    /***********************************************************************
    * Write out the body of the comment.                                   *
    ***********************************************************************/
    String curOutput = "" ;
      /*********************************************************************
      * The current output line.                                           *
      * Invariant: ~openPar => (curOutput = "")                            *
      *********************************************************************/
    boolean openPar = false ;
      /*********************************************************************
      * True if we are writing tokens inside a LaTeXCommentPar.            *
      *********************************************************************/
    boolean openVerb = false ;
      /*********************************************************************
      * True if currently writing tokens inside a verbatim environment.    *
      * Invariant: openVerb => openPar                                     *
      *********************************************************************/
    boolean openMath = false ;
      /*********************************************************************
      * True if we are writing tokens inside an \ensuremath argument.      *
      * Invariant: openMath => openPar                                     *
      *********************************************************************/
    boolean openLabel = false ;
      /*********************************************************************
      * openLabel is true iff we are writing tokens inside the label       *
      * argument of a LaTeXCommentPar environment.  In that case,          *
      * curOutput is the output for the label constructed thus far.        *
      *********************************************************************/
    int item = 0;
     /**********************************************************************
     * The next token to process is com[line][item].                       *
     **********************************************************************/
    while (line < endLine)
     { // BEGIN while (line < endLine)
      /*********************************************************************
      * Writing out next line.                                             *
      *                                                                    *
      * Invariant: curOutput = "".                                         *
      *********************************************************************/
      if (lineType[line] == -2)
       {                  // BEGIN then OF if ((lineType[line] == -2)...)
        /*******************************************************************
        * This is a blank line.  Close the current paragraph and write     *
        * out a LaTeXCommentVSpaceCmd command.                             *
        *******************************************************************/
         if (openPar)
           /****************************************************************
           * Close an open paragraph.                                      *
           ****************************************************************/
          { CloseParagraph(writer, curOutput, openMath, openVerb) ;
            openPar   = false ;
            openMath  = false ;
            openVerb  = false ;
            curOutput = "" ;
          } ;

         /******************************************************************
         * Set numOfBlankLines to the number of blank lines before the     *
         * next paragraph, and increment line by numOfBlankLines - 1.      *
         ******************************************************************/
         int numOfBlankLines = 0 ;
         while (lineType[line] == -2)
          { numOfBlankLines = numOfBlankLines + 1 ;
            line = line + 1 ;
          }
         line = line - 1;

         /******************************************************************
         * Write out a LaTeXCommentVSpaceCmd command.                      *
         ******************************************************************/
         writer.putLine(
           Parameters.LaTeXCommentVSpaceCmd +"{" + 
           Misc.floatToString(Parameters.LaTeXCommentVSpace(numOfBlankLines),
                              2)
           + "}%");
       }                   // END then OF if ((lineType[line] == -2)...)

      else
       {                   // BEGIN else OF if ((lineType[line] == -2)...)
         /******************************************************************
         * This is a non-blank line.                                       *
         ******************************************************************/
         if (lineType[line] != -1) 
          {                             // BEGIN if (lineType[line] != -1)
           /****************************************************************
           * This line begins a new paragraph, so write parStart[line].    *
           ****************************************************************/
           if (openPar)
            { /*************************************************************
              * Need to start new paragraph, but old one is still open.    *
              * So, need to close it.                                      *
              *************************************************************/
              CloseParagraph(writer, curOutput, openMath, openVerb) ;
              openMath  = false ;
              openVerb  = false ;
              curOutput = "" ;
            } ;

           writer.putLine(parStart[line]);
           openPar = true ;
           Debug.Assert(!(openVerb || openMath),
             "FormatComments.InnerWriteComment: Invariant "
           + "(openMath \\/ openVerb) => openPar  violated") ;
          
           /****************************************************************
           * Set openLabel true iff this is a labeled paragraph.           *
           ****************************************************************/
           openLabel = false ;
           if (lineType[line] > 0)
             { openLabel = true; }
         }                              // END if (lineType[line] != -1) 
        /*******************************************************************
        * Now, process the tokens on this line, which should be non-blank. *
        *******************************************************************/
        Debug.Assert(curOutput.equals(""),
                     "FormatComments.InnerWriteComment: Output not processed\n"
                     + "    when it should have been");

        item = 0 ;
        while (item < com[line].length)
         {                         // BEGIN while (item < com[item].length)

          /*****************************************************************
          * Loop Invariant: openLabel => item \leq offSet                  *
          *****************************************************************/
          if (openLabel && (item == lineType[line]))
           { if (openMath)
               { /**********************************************************
                 * Have to close the \ensuremath.                          *
                 **********************************************************/
                 curOutput = curOutput + "}";
                 openMath = false;
               } ;
             Misc.BreakStringOut (writer, curOutput + "}%") ;
             curOutput = "";
             openLabel = false;
           }

          if (com[line][item].type == CToken.VERB)
           { /**************************************************************
             * This is a VERB token.                                       *
             **************************************************************/
             if (openMath)
              { curOutput = curOutput + "}" ;
                openMath = false; } ;

             if (IsParType(commentType) && (! openLabel) && (item == 0))
              /*************************************************************
              * We write a verbatim command only if this is not a          *
              * one-line comment, we're not inside a label, and this is    *
              * the first item on the line.  Otherwise, we just TeXify     *
              * the string and write it out.  (A \verb command won't work  *
              * because TeX may process the string inside a command        *
              * argument.)                                                 *
              *************************************************************/
              { Debug.Assert(curOutput.equals(""),
                  "FormatComments.InnerWriteComment: "
                   + "failed to write curOutput");
                if (! openVerb)
                  {writer.putLine("\\begin{minipage}[t]{\\linewidth}");
                     /******************************************************
                     * A verbatim environment is put inside a minipage     *
                     * environment so it won't be broken across pages.     *
                     ******************************************************/
                   writer.putLine("\\begin{verbatim}") ;

                   openVerb = true;
                   /********************************************************
                   * Set curOutput to a number of spaces equal to the      *
                   * number of spaces to the left of the "`.", if this     *
                   * token begins a VERB.                                  *
                   ********************************************************/
                   int w = com[line][item].column;
                   while (w > 0)
                    { curOutput = curOutput + " ";
                      w = w - 1;
                    }
                  } ;

                writer.putLine(curOutput + com[line][0].string) ;
                curOutput = "";
              }
             else
              { curOutput = curOutput + Misc.TeXify(com[line][item].string) ;
              }
           }       
          else
           {       // BEGIN else OF if (com[line][item].type == CToken.VERB)
             /**************************************************************
             * This is not a VERB token.                                   *
             *                                                             *
             * Check if need to close a verbatim environment.              *
             **************************************************************/
             if (openVerb)
              { writer.putLine("\\end{verbatim}%") ;
                writer.putLine("\\end{minipage}");
                openVerb = false;
              } ;

             CToken tok  = com[line][item] ;
             CToken ptok = previousCToken(com, line, item) ;
               /************************************************************
               * tok is the current token, and ptok is the preceding one.  *
               ************************************************************/

             /**************************************************************
             * Check if need to close \ensuremath command.                 *
             **************************************************************/
             if (   openMath 
                 && (   !tok.isTLA
                     || (tok.type == CToken.TEX)))
                        /***************************************************
                        * We close \ensuremath for a TEX token that        *
                        * somehow mangaged to get marked as a TLA token.   *
                        * (For example, it might have been inside a        *
                        * "`...'".)                                        *
                        ***************************************************/
               { curOutput = curOutput + "}" ;
                 openMath = false;}

             /**************************************************************
             * Output a space if this there is a space between this token  *
             * and the preceding one--and this token doesn't either begin  *
             * a paragraph or come right after the label in a labeled      *
             * paragraph.                                                  *
             *                                                             *
             * If both tokens are on the same line and there are at least  *
             * 5 spaces between them, then leave a fair amount of extra    *
             * space between them, based on how many spaces apart they     *
             * are.  (I chose 4 spaces because "`foo'  bar" winds up with  *
             * 5 apparent spaces between the "`foo'" and the "bar".        *
             *                                                             *
             * If both tokens are in in math mode and their types          *
             * indicate that they probably shouldn't be printed right      *
             * next to one another, so we add a space.  (In this case,     *
             * either we've made a mistake in identifying TLA tokens, or   *
             * the input is strange.  Adding a space in the output seems   *
             * like the best thing to do here.)  Outputing a "\ " doesn't  *
             * work because that doesn't seem to permit a line break in    *
             * math mode.  So, we add "} \ensuremath{".                    *
             **************************************************************/
             if (   !isPreviousAdjacent(com, line, item)
                 && !(   (lineType[line] >= 0)
                      && (   (item == 0)
                          || (item == lineType[line]))))
               { 

                if (   (item > 0)
                    && (ptok.column + ptok.getWidth() <= tok.column - 5))
                 { curOutput = 
                    curOutput + Parameters.LaTeXSpaceCommand
                     + "{" 
                     + Misc.floatToString(
                           Parameters.LaTeXCommentLeftSpace(
                               tok.column - (ptok.column + ptok.getWidth())),
                           2) + "}";
                 }
                else
                 {
                  if(   (tok.isTLA) && (ptok.isTLA)
                     && (   (tok.type  != CToken.BUILTIN)
                         || (BuiltInSymbols.GetBuiltInSymbol(
                              tok.string, true).symbolType == Symbol.PREFIX)
                         || (BuiltInSymbols.GetBuiltInSymbol(
                              tok.string, true).symbolType == Symbol.KEYWORD))
                     && (tok.type  != CToken.RIGHT_DQUOTE)
                     && (   (ptok.type != CToken.BUILTIN)
                         || (BuiltInSymbols.GetBuiltInSymbol(
                              ptok.string, true).symbolType == Symbol.POSTFIX)
                         || (BuiltInSymbols.GetBuiltInSymbol(
                              ptok.string, true).symbolType == Symbol.KEYWORD))
                     && (ptok.type != CToken.LEFT_DQUOTE))
                   { curOutput = curOutput + "} \\ensuremath{"; 
                   }
                  else
                   { curOutput = curOutput + " "; 
                   } ;
                 }
               } ;
             /**************************************************************
             * Check if need to start an \ensuremath argument.             *
             **************************************************************/
             if ( (!openMath) && tok.isTLA)
               { curOutput = curOutput + "\\ensuremath{" ;
                 openMath  = true;}

             /**************************************************************
             * Output the token.                                           *
             **************************************************************/
             switch (tok.type)
              {
               case CToken.BUILTIN :
                 if (tok.isTLA)
                  { curOutput = curOutput + 
                     BuiltInSymbols.GetBuiltInSymbol(tok.string, true).TeXString;
                   /********************************************************
                   * For subscripted BUILINs like WF_, we don't do         *
                   * subscripting in comments, so we must print the "_".   *
                   ********************************************************/
                   if (   (tok.string.charAt(tok.string.length()-1) == '_')      
                       && (tok.string.length() != 1))
                    { curOutput = curOutput + "\\_"; } ;
                  }
                 else
                  { curOutput = curOutput + 
                      getAmbiguous(tok.string);
                  } ;
                 break ;

               case CToken.NUMBER :
                 curOutput = curOutput + Misc.TeXify(tok.string);
                                /*******************************************
                                * Need to TeXify because of numbers like   *
                                * "\O777".                                 *
                                *******************************************/
                 break ;        

               case CToken.STRING :
                 curOutput = curOutput + Parameters.LaTeXStringCommand 
                             + "{" + Misc.TeXify(tok.string) + "}" ;
                 break ;

               case CToken.PF_STEP :
                 curOutput = curOutput + LaTeXOutput.PfStepString(tok.string) ;
                 break ;

               case CToken.IDENT :
                 curOutput = curOutput + Misc.TeXifyIdent(tok.string);
                 break ;

               case CToken.OTHER :
                 curOutput = curOutput + Misc.TeXify(tok.string);
                 break ;

               case CToken.REP_CHAR :
                 /**********************************************************
                 * Set outS to the command to produce the token.           *
                 **********************************************************/
                 String outS = getRepeatCharCommand(tok.string.charAt(0));
                 if (outS.equals(""))
                  { outS = Misc.TeXify(tok.string);
                  }
                 else
                  { outS = outS + "{" + tok.getWidth() + "}";
                  } ;
                 /**********************************************************
                 * If this token is on a line by itself, then typeset it   *
                 * on a line by itself.                                    *
                 **********************************************************/
                 if (com[line].length == 1)
                  { if (lineType[line] == -1)
                      /*****************************************************
                      * If this isn't the first line of the paragraph,     *
                      * must output a \par command first.                  *
                      *****************************************************/
                      { outS = "{\\par}" + outS ;
                      } ;
                   if (   (line + 1 < lineType.length)
                       && (lineType[line + 1] == -1) )
                      /*****************************************************
                      * If this isn't the last line of the paragraph,      *
                      * must output a \par command afterwards.             *
                      *****************************************************/
                      { outS = outS + "{\\par}" ; 
                      } ;
                  } ;
                 curOutput = curOutput + outS ;
                break ;

               case CToken.LEFT_DQUOTE :
                 if (tok.isTLA)
                   {curOutput = curOutput + "\\mbox{``}" ; }
                 else
                   {curOutput = curOutput + "``" ; }
                 break ;

               case CToken.RIGHT_DQUOTE :
                 if (tok.isTLA)
                   {curOutput = curOutput + "\\mbox{''}" ; }
                 else
                   {curOutput = curOutput + "''" ; }
                 break ;

               case CToken.TEX :
                 curOutput = curOutput + tok.string;
                 break ;

               default :
                 Debug.ReportBug(
                   "Bad CToken type found in FormatComments.InnerWriteComment");
                 break ;
              }
        
           }       // END else OF if (com[line][item].type == CToken.VERB)

          item = item + 1;
         }                        // END while (item < com[item].length)
       };                      // END else OF if ((lineType[line] == -2)...)
     
      Misc.WriteIfNonNull(writer, curOutput);
      curOutput = "" ;
      line = line + 1;
     }; // END while (line < endLine)

    /***********************************************************************
    * Write out the end of the comment.                                    *
    *                                                                      *
    * Start by closing any open \ensuremath command or verbatim            *
    * environment.                                                         *
    ***********************************************************************/
    if (IsParType(commentType) && openPar)
      { CloseParagraph(writer, curOutput, openMath, openVerb) ;
        curOutput = ""; }
    else
      { if (openMath)
          { curOutput = curOutput + "}" ; 
          } ;
      } ;
    switch (commentType)
      {
       case ONE_LINE :
       case ZERO_WIDTH :
         Misc.BreakStringOut(writer, curOutput + "}%");
         break ;
       case PAR :
         Misc.WriteIfNonNull(writer, curOutput);
         writer.putLine("\\end{" + Parameters.LaTeXLeftMultiLineComment + "}%");
         break ;
       case RIGHT_MULTI :
         Misc.WriteIfNonNull(writer, curOutput);
         writer.putLine("\\end{" + Parameters.LaTeXRightMultiLineComment
                                    + "}%");
         break ;
       default :
         Debug.ReportBug(
           "The impossible happened in FormatComments.InnerWriteComment");
      };
      
   } // END InnerWriteComment(...)

  public static final int ONE_LINE    = 1;
  public static final int ZERO_WIDTH  = 2;
  public static final int PAR         = 3;
  public static final int RIGHT_MULTI = 4;
    /***********************************************************************
    * The possible commentType arguments to writeComment.                  *
    ***********************************************************************/
    
  private static boolean IsParType(int type)
    /***********************************************************************
    * True if type is PAR or RIGHT_MULTI.                                  *
    ***********************************************************************/
    { return (type == PAR) || (type == RIGHT_MULTI) ;
    }    

  private static void CloseParagraph
                      (OutputFileWriter writer, 
                       String  curOutput, 
                       boolean openMath, 
                       boolean openVerb)
    /***********************************************************************
    * A procedure for InnerWriteComments that closes the current           *
    * paragraph.  After this is called, the caller should execute:         *
    *                                                                      *
    *    openPar   = false ;                                               *
    *    openMath  = false ;                                               *
    *    openVerb  = false ;                                               *
    *    curOutput = "" ;                                                  *
    ***********************************************************************/
    { String curOut = curOutput ;
      if (openMath)
       { curOut = curOut + "}%" ; } ;
      if (openVerb)
       { Misc.WriteIfNonNull(writer, curOut);
         curOut = "" ;
         writer.putLine("\\end{verbatim}");
         writer.putLine("\\end{minipage}");
           /****************************************************************
           * Note: a verbatim environment is put inside a minipage         *
           * environment so it won't be broken across pages.               *
           ****************************************************************/
       } ; 
      Misc.WriteIfNonNull(writer, curOut);
      writer.putLine("\\end{" + Parameters.LaTeXCommentPar + "}%");
    } ;
    

  private static boolean HasDigit(String str)
   { int i = 0 ;
     boolean result = false ;
     while ((!result) && (i < str.length()))
      { result = Misc.IsDigit(str.charAt(i));
        i = i + 1;
      } ;
     return result;
   }

} // END Class

/* Last modified on Wed 19 Sep 2007 at  5:26:37 PST by lamport */ 
/*      modified on Tue Dec 12 14:39:45 PT 2000 by unknown */ 
