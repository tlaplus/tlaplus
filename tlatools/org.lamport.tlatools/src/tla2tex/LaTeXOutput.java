// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS LaTeXOutput                                                        *
*                                                                          *
* This class defines the following static methods (aka procedures) for     *
* writing the LaTeX output.                                                *
*                                                                          *
*   WriteAlignmentFile(Token[][])                                          *
*      For tlatex.TLA, writes the LaTeX source file whose resulting        *
*      log file contains the dimensions needed to do the alignment.        *
*                                                                          *
*   WriteTeXAlignmentFile(Token[][], Vector, float)                        *
*      For tlatex.TeX, writes the LaTeX source file whose resulting        *
*      log file contains the dimensions needed to do the alignment.        *
*                                                                          *
*   RunLaTeX(fileName)                                                     *
*      Runs LaTeX on fileName.tex.                                         *
*                                                                          *
*   SetDimensions(Token[][])                                               *
*      Sets distFromMargin and preSpace for all the tokens in the spec,    *
*      using the log file produced by LaTeX'ing the alignment file.        *
*                                                                          *
*   WriteLaTeXFile(Token[][])                                              *
*      Writes the final output file for tlatex.TLA.                        *
*                                                                          *
*   WriteTLATeXEnvironment(Token[][], OutputFileWriter)                    *
*      Writes a single tlatex environment for tlatex.TeX.                  *
*                                                                          *
* Note: The methods InnerWriteAlignmentFile and InnerWriteLaTeXFile have   *
* the following bug.  If the user types something like x^2^3, the methods  *
* produce the LaTeX input x^{2}^{3}, which produces a TeX "double          *
* superscript" error.  However, since this is illegal TLA+ and TeX         *
* handles the error appropriately in \batchmode, I have not bothered to    *
* correct this.                                                            *
***************************************************************************/
package tla2tex;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Vector;

import util.ToolIO;


public final class LaTeXOutput
{   
public static void WriteAlignmentFile(Token[][] spec)
  { OutputFileWriter writer = 
         StartLaTeXOutput(Parameters.LaTeXAlignmentFile);
    InnerWriteAlignmentFile(spec, writer, true);
    return;
  }

public static void WriteTeXAlignmentFile(Token[][] spec, 
                                         Vector preamble,
                                         float  linewidth)
  /*************************************************************************
  * Called to write the alignment file for a tlatex environment, where     *
  * preamble is a vector of strings that form the preamble.  The           *
  * alignment file sets \textwidth to the linewidth value, unless          *
  * linewidth <= 0, in which case it uses whatever value the preamble      *
  * sets \textwidth to.                                                    *
  *************************************************************************/
 {OutputFileWriter writer = 
    new OutputFileWriter(Parameters.LaTeXAlignmentFile + ".tex");

  /*************************************************************************
  * Write the \batchmode command to suppress most terminal output.         *
  *************************************************************************/
  writer.putLine("\\batchmode");
  int i = 0 ;
  while (i < preamble.size())
   { writer.putLine((String) preamble.elementAt(i)) ;
     i = i + 1;
   } ;
  if (linewidth >= 0)
   { writer.putLine("\\setlength{\\textwidth}{" 
                     + Misc.floatToString(linewidth, 2) + "pt}");
     // see below for why this is commented out.
     //writer.putLine("\\makeatletter") ;   // added by LL on 7 Aug 2012
   } ;
  writer.putLine("\\begin{document}");
  // We need to put the \makeatletter command after the \begin{document}
  // because it appears that the beamer style and probably others cause
  // the \begin{document} command to reset the catcoding of @ to "other".
  // I don't know why I added the \makeatletter command only if linewidth >=0,
  // which seems to be the case only if the number of environments is different
  // this time than the last time tlatex was run.  However, it seems like 
  // there's no reason not to write the \makeatletter command in that case.
  // Hence the following statement was added by LL on 21 Feb 2013.
  writer.putLine("\\makeatletter"); 

  /*************************************************************************
  * Define \% to have its usual meaning, in case it is redefined by the    *
  * preamble.                                                              *
  *************************************************************************/
  writer.putLine("\\chardef\\%=`\\%");
  InnerWriteAlignmentFile(spec, writer, false) ;
 }

private static void InnerWriteAlignmentFile(Token[][] spec, 
                                            OutputFileWriter writer,
                                            boolean tlaMode)
  /*************************************************************************
  * Writes the body of the file (everything between the \begin{document}   *
  * and \end{document}), plus the \end{document}, for the                  *
  * WriteAlignmentFile method.  Also used to write the body of a tlatex    *
  * environment for the WriteTeXAlignmentFile method.  It is called with   *
  * the tlaMode flag true by WriteLaTeXFile and with it false by           *
  * WriteTLATeXEnvironment.                                                *
  *************************************************************************/
  { int line = 0 ;
      /*********************************************************************
      * line is the current line of the spec being ouput.                  *
      *********************************************************************/

    /***********************************************************************
    * Skip over prolog lines.                                              *
    ***********************************************************************/
    boolean inProlog = true ;
    while (inProlog && (line < spec.length))
       { if (    (spec[line].length > 0)
              && (spec[line][0].type != Token.PROLOG))
           { inProlog = false;}
         else
           { line = line + 1;}
       };

    /***********************************************************************
    * If shading is specified, then we typeset the alignment file with     *
    * LaTeX's shading flag set true--just in case that affects the width   *
    * of comments used in alignments.                                      *
    ***********************************************************************/
    if (Parameters.CommentShading)
     {writer.putLine("\\setboolean{shading}{true}") ;}

    boolean inBeginModule = false ;
      /*********************************************************************
      * True iff we have output the first "----" of                        *
      * "---- MODULE foo ----" but not the second.                         *
      *********************************************************************/

    boolean inSub = false;
         /******************************************************************
         * True while putting out sub/superscript tokens.                  *
         ******************************************************************/
      
    while (line < spec.length)
     { int item = 0 ;
         /******************************************************************
         * item is the current item of the current line.                   *
         ******************************************************************/
         
       String outLine = Parameters.LaTeXStartAlignLine + "{"; ;

       while (item < spec[line].length)
        /*******************************************************************
        * There's no need to produce output for blank lines, so we just    *
        * skip them.                                                       *
        *******************************************************************/
        { 
          Token tok = spec[line][item] ;
            /***************************************************************
            * The current token.                                           *
            ***************************************************************/

          if (inSub && (! tok.subscript))
            { /*************************************************************
              * The current subcript has ended; close the command's "}".   *
              *************************************************************/
              inSub = false ;
              outLine = outLine + "}";
            } ;
               
           if (tok.isAlignmentPoint)
              { outLine = outLine + "}" + Parameters.LaTeXAlignPoint + "{"
                            + line + "}{" + item + "}{" ; 
              };
          switch (tok.type)
           { case Token.BUILTIN :
               int symType = BuiltInSymbols.GetBuiltInSymbol(
                                       spec[line][item].string, true).symbolType ;
                 /**********************************************************
                 * Check if we should start a sub/superscript.             *
                 **********************************************************/
                 if (   (! inSub)
                     && (   (symType == Symbol.SUBSCRIPTED)
                         || tok.string.equals("^"))
                     && (item + 1 < spec[line].length)
                     && spec[line][item+1].subscript )
                        /***************************************************
                        * A subscripted/superscrip symbol (like "]_" or    *
                        * "^") begins a sub/superscript iff it is          *
                        * followed by a subscript token on the same line.  *
                        ***************************************************/
                  { /*******************************************************
                    * This starts a sub or superscript.                    *
                    *******************************************************/
                    inSub = true ;
                    if (symType == Symbol.SUBSCRIPTED)
                     { /****************************************************
                       * It's a subscript.                                 *
                       ****************************************************/
                       outLine = outLine + " " +  
                          BuiltInSymbols.GetBuiltInSymbol(
                                                   tok.string, true).TeXString
                          + "_{";
                     }    
                    else
                     { /****************************************************
                       * It's a superscript.                               *
                       ****************************************************/
                       outLine = outLine + " " + "^{";
                     }    
                  } // END then OF if if (   (! inSub) ... )
                 else
                  { /*******************************************************
                    * Not a sub/superscript.  Output a space followed by   *
                    * the symbol.  (It's always safe to put a space in a   *
                    * specification line, since it's typeset in math       *
                    * mode.                                                *
                    *******************************************************/
                    outLine = outLine + " " +  
                     BuiltInSymbols.GetBuiltInSymbol(tok.string, true).TeXString;
                  }; // END else OF if if (   (! inSub) ... )
               break ;

             case Token.NUMBER :
             case Token.IDENT :
               outLine = outLine + " " + Misc.TeXify(tok.string) ; 
                 /**********************************************************
                 * We TeXify the string to typeset a "\" from a number or  *
                 * a "_" from an identifier.                               *
                 **********************************************************/
               break ;
               
             case Token.PCAL_LABEL :
               outLine = outLine + " " + Misc.TeXifyPcalLabel(tok.string) ;
               break ;

             case Token.STRING :
               outLine = outLine + Parameters.LaTeXStringCommand + "{"  
                           + FixString(tok.string) + "}";
               break ;

             case Token.PF_STEP :
               outLine = outLine + PfStepString(tok.string) ;
               if ( ((Token.PfStepToken) tok).needsSpace )
                 {outLine = outLine + "\\ "; } ;
               break ;

             case Token.COMMENT :
               CommentToken ctok = (CommentToken) tok ;
               switch (ctok.subtype)
                { case CommentToken.ONE_LINE :
                    if (item != 0)
                      /*****************************************************
                      * If the first item is a comment, then it is either  *
                      * a left-comment or else the only token on the       *
                      * line.  If it's a left-comment token, it's going    *
                      * to be typeset with width zero, so we can omit it   *
                      * in the alignment file.  If it's the only token on  *
                      * the line, we don't need to output it in the        *
                      * alignment file.                                    *
                      *****************************************************/
                      { outLine = outLine + "%";
                        Misc.WriteIfNonNull(writer, outLine);
                        outLine = "" ;
                        Vector vec = new Vector(2);
                        vec.addElement(tok.string) ;
                        FormatComments.WriteComment
                         (writer, vec, FormatComments.ONE_LINE, 0, tlaMode) ;
                      };
                    break ;

                  case CommentToken.BEGIN_MULTI :
                  case CommentToken.NULL :
                  case CommentToken.MULTI :
                  case CommentToken.PAR :
                    /*******************************************************
                    * No alignment output is needed for a multi-line       *
                    * comment, which must be at the end of the line.       *
                    *******************************************************/
                    break ;

                  default :
                  Debug.ReportBug(
                     "Bad comment token subtype at position (" 
                         + line + ", " + item + ")\n"
                    + "    in LaTeXOutput.WriteAlignmentFile");

                } ; // END switch (ctok.subtype)
               break ;

             case Token.DASHES :
               if (inBeginModule)
                { /*********************************************************
                  * Ending a "--- MODULE foo ---".                         *
                  *********************************************************/
                  outLine = outLine + "}" + Parameters.LaTeXAlignRightDash 
                              + "{" ;
                  inBeginModule = false ;
                }  // END THEN if (inBeginModule)
               else
                { if (   (item + 1 < spec[line].length)
                       && (spec[line][item+1].string.equals("MODULE")))
                   { /******************************************************
                     * Starting a "--- MODULE foo ---".                    *
                     ******************************************************/
                     outLine = outLine + "}" + 
                                Parameters.LaTeXAlignLeftDash + "{" ;
                     inBeginModule = true ;
                   } // END THEN of if ( (item + 1 < ... ))
                  else
                   { /******************************************************
                     * This is a mid-module dash.                          *
                     ******************************************************/
                     outLine = outLine + "}" + Parameters.LaTeXAlignDash 
                                 + "{" ;
                   } // END ELSE of if ( (item + 1 < ... ))

                } ; // END ELSE if (inBeginModule)
               break ;

             case Token.END_MODULE :
               outLine = outLine + "}" + Parameters.LaTeXAlignEndModule 
                           + "{";
               break ;

             case Token.EPILOG :
               /************************************************************
               * No output needed for an epilog token.                     *
               ************************************************************/
               break ;

             default :
               Debug.ReportBug(
                    "Bad token type at position (" + line + ", " 
                         + item + ")\n"
                  + "    in LaTeXOutput.WriteAlignmentFile");

           };  // END switch (tok.type)

          item = item + 1;
        }; // END while (item < spec[line].length)

       /********************************************************************
       * End the current line.                                             *
       ********************************************************************/
       if (inSub) 
        { /*****************************************************************
          * If inside a sub/superscript, have to close the "^{" or "_{".   *
          *****************************************************************/
          outLine = outLine + "}";
          inSub = false ;
        };         
       outLine = outLine + "}";
       Misc.BreakStringOut(writer, outLine);
       line = line + 1;
     }; // END while (line < spec.length)

    /***********************************************************************
    * End of the specification; end the output file.                       *
    ***********************************************************************/
    writer.putLine("\\end{document}");
    writer.close(); 
  } ;


/* ----------------------------------------------------------------------- */


  private static OutputFileWriter StartLaTeXOutput(String fileName)
  /*************************************************************************
  * Opens writer on the file fileName.tex and writes the beginning of the  *
  * file, through the \begin{document}.                                    *
  *************************************************************************/
  { 
    /***********************************************************************
    * Open the OutputFileWriter.                                           *
    ***********************************************************************/
    OutputFileWriter writer = 
        new OutputFileWriter(prependMetaDirToFileName(fileName) + ".tex");

    /***********************************************************************
    * Write \batchmode and \documentclass commands.  (We use \batchmode    *
    * because (a) we don't want to generate much terminal output, and (b)  *
    * we want TeX to carry on in the face of an error--which should be     *
    * minor.  (In additionb to the problem mentioned at the beginning of   *
    * this file, bad `^...^' input in a comment can produce a LaTeX file   *
    * that generates a TeX error.)                                         *
    ***********************************************************************/
    writer.putLine("\\batchmode %% Suppresses most terminal output.");
    if (Parameters.LaTeXptSize == 10)
      {writer.putLine("\\documentclass{article}");}
    else
      {writer.putLine("\\documentclass[" + Parameters.LaTeXptSize
                                        + "pt]{article}");};
    /***********************************************************************
    * Add commands for making shaded comments only if shading requested.   *
    ***********************************************************************/
    if (Parameters.CommentShading)
      { writer.putLine("\\usepackage{color}") ;
        writer.putLine("\\definecolor{boxshade}{gray}{" + 
                       Parameters.PSGrayLevel + "}") ;
      }

    /***********************************************************************
    * Write commands for setting \textwidth, \textheight, \hoffset, and    *
    * \voffset.                                                            *
    ***********************************************************************/
    writer.putLine(
        "\\setlength{\\textwidth}{" + Parameters.LaTeXtextwidth + "pt}");
    writer.putLine(
        "\\setlength{\\textheight}{" + Parameters.LaTeXtextheight + "pt}");
    if (Parameters.LaTeXhoffset != 0)
      { writer.putLine(
        "\\addtolength{\\hoffset}{" + Parameters.LaTeXhoffset + "pt}");
      } ;
    if (Parameters.LaTeXvoffset != 0)
      { writer.putLine(
        "\\addtolength{\\voffset}{" + Parameters.LaTeXvoffset + "pt}");
      } ;


    /***********************************************************************
    * Either add the LaTeXStyleFile to the beginning of the output, or     *
    * else add a usepackage command to read the user-specified -style      *
    * package.                                                             *
    ***********************************************************************/
    if (Parameters.UserStyleFile.equals(""))
      { ResourceFileReader latexStyleReader 
                     = new ResourceFileReader(Parameters.LaTeXStyleFile);
        CopyResourceFile(latexStyleReader, writer);
      }
    else
      { writer.putLine("\\usepackage{" + Parameters.UserStyleFile + "}");
      } ;

    writer.putLine("\\begin{document}");
    writer.putLine("\\tlatex");
      /*********************************************************************
      * Add a \tlatex command, which causes TeX to do the following:       *
      *   - Make "@" a letter, since some special commands                 *
      *     use "@" in their name.                                         *
      *   - Define \% to its standard meaning.                             *
      *   - Set \parindent to 0.                                           *
      *********************************************************************/
    return writer ;
  }


  private static void CopyResourceFile(ResourceFileReader input, 
                                OutputFileWriter output)
  /*************************************************************************
  * Copies the complete input file to the output file, but does not close  *
  * the output file.                                                       *
  *************************************************************************/
  { 
    String line = input.getLine();
    while (line != null)
      { output.putLine(line) ;
        line = input.getLine() ;
      } ;
    input.close();
  }  


/* ----------------------------------------------------------------------- */


  public static void RunLaTeX(String fileName)
    /***********************************************************************
    * Runs LaTeX on the file fileName.tex.                                 *
    * Modified on 11 November 2001 to call ExecuteCommand.                 *
    ***********************************************************************/
    { String latexCmd = Parameters.LaTeXCommand + " " + fileName + ".tex";
      ExecuteCommand.executeCommand(latexCmd);
    }    


/* ----------------------------------------------------------------------- */


  public static void SetDimensions(Token[][] spec)
  { /***********************************************************************
    * Read the log file and set the distFromMargin fields.                 *
    *                                                                      *
    * First, open log file.                                                *
    ***********************************************************************/
    BufferedReader bufferedReader = null ;
    try 
     { bufferedReader = 
         new BufferedReader(new InputStreamReader(
           new FileInputStream(prependMetaDirToFileName(Parameters.LaTeXAlignmentFile + ".log")))) ;
     }
    catch (FileNotFoundException e)
     { /**************************************************************
       * File fileName could not be found.                           *
       **************************************************************/
       Debug.ReportError(
          "Could not read file " + Parameters.LaTeXAlignmentFile + ".log\n"
        + "    written by LaTeX");
     } ;

   /************************************************************************
   * Next, read log file.                                                  *
   ************************************************************************/
   try 
    { String inputLine = bufferedReader.readLine();

      while (inputLine != null)
       { if (   (inputLine.length() > 2)
             && (inputLine.substring(0,3).equals("\\%{")))
          { int start = 3 ;
            int after = inputLine.indexOf("}",start) ;
            int line  = Integer.parseInt(inputLine.substring(start, after));
            start = after + 2;
            after = inputLine.indexOf("}",start) ;
            int item = Integer.parseInt(inputLine.substring(start, after));
            start = after + 2;
            after = inputLine.indexOf("p",start) ;
            float dist = Misc.stringToFloat(inputLine.substring(start, after));
            spec[line][item].distFromMargin = dist;
          }; // END if (   (inputLine.length() > 2) ... )
         inputLine = bufferedReader.readLine();
       } // END while (inputLine != null)
    }
   catch (IOException e)
    { Debug.ReportError(
         "Error reading file: "  + Parameters.LaTeXAlignmentFile + ".log\n"
       + "    written by LaTeX");
          };

   /************************************************************************
   * Now, set posCols to be a sorted array of all the PosAndCol objects       *
   * corresponding to tokens in the spec.                                  *
   *                                                                       *
   * First compute the dimension of the array.                             *
   ************************************************************************/
   int line = 0 ;
   int arrayLen = 0 ;
   while (line < spec.length)
    { arrayLen = arrayLen + spec[line].length ;
      line = line + 1;
    };
   
   /************************************************************************
   * Next add all PosAndCol objects to the array and sort it.              *
   ************************************************************************/
   PosAndCol[] posCols = new PosAndCol[arrayLen] ;
   int arrayItem = 0 ;
   line = 0 ;
   while (line < spec.length)
    { int item = 0 ;
      while (item < spec[line].length)
       { posCols[arrayItem] = 
             new PosAndCol(line, item, spec[line][item].column) ;
         item = item + 1;
         arrayItem = arrayItem + 1;
       } ;
      line = line + 1;
    } ;   

   PosAndCol.sort(posCols);

   /************************************************************************
   * Compute preSpace fields for tokens in the order they appear in the    *
   * posCols array.                                                        *
   ************************************************************************/
   /*
    * On 1 Aug 2012, LL made the following observation and change.  The
    * code ignored tok.belowAlign if tok.aboveAlign was specified.  It was
    * possible for both to be specified, so this caused a mis-alignment in
    * rare cases--in particular, if the above alignment didn't move the
    * token far enough to the right to be above or to the right of the token
    * below it that was aligning itself with it.  Therefore, I changed the code 
    * to set preSpace to the maximum of the values computed for an aboveAlignment 
    * and a belowAlignment.
    */
   int nextPos = 0 ;
   while (nextPos < posCols.length)
    { PosAndCol pc = posCols[nextPos] ;
      Token tok = pc.toToken(spec) ;
      Debug.Assert(tok.preSpace == 0,
           "preSpace already computed when it shouldn't have been");
      if (tok.belowAlign.line != -1)
           { /**************************************************************
             * tok begins an inner-alignment.                              *
             **************************************************************/

             /**************************************************************
             * Set maxIndent to the maximum of the current indentation of  *
             * all tokens in the alignment.                                *
             **************************************************************/
             float tokIndent = 
                  TotalIndent(spec, new Position(pc.line, pc.item));
             float maxIndent = tokIndent ;
             Position alPos = tok.belowAlign ;
             while (alPos.line != -1)
              { float f = TotalIndent(spec, alPos);
                if (f > maxIndent) { maxIndent = f; } ;
                alPos = alPos.toToken(spec).belowAlign ;
              } ;

             /**************************************************************
             * Set preSpace to the difference between maxIndent and the    *
             * token's own current indentation.                            *
             **************************************************************/
             tok.preSpace = maxIndent - tokIndent ;

             /**************************************************************
             * Add extra space according to the minimum of the number of   *
             * extra spaces between each token in the alignment and the    *
             * non-left-comment token to its left (if there is one).       *
             * 
               Why is this minimum and not maximum??
               I suspect it's because TotalIndent was set to the maximum
               indent without taking into account the blank columns to
               the left of the token.  Therefore, the token with maximum 
               TotalIndent should have the minimum number of spaces to
               its left--in most cases.
               
             **************************************************************/
             Token ltok = null ;
             int extraSpace = Integer.MAX_VALUE;

             if (   (pc.item > 1)
                 || (   (pc.item == 1)
                     && (spec[pc.line][0].type != Token.COMMENT)))
               { ltok = spec[pc.line][pc.item - 1] ;
                 extraSpace = tok.column - (ltok.column + ltok.getWidth());
               };
             alPos = tok.belowAlign ;
             while (alPos.line != -1)
              { if (   (alPos.item > 1)
                    || (   (alPos.item == 1)
                        && (spec[alPos.line][0].type != Token.COMMENT)))
                  { ltok = spec[alPos.line][alPos.item - 1] ;
                    int sp = alPos.toToken(spec).column 
                                   - (ltok.column + ltok.getWidth());
                    if (sp <  extraSpace) { extraSpace = sp ;};
                  };
                alPos = alPos.toToken(spec).belowAlign ;
              } ;
             if (extraSpace == Integer.MAX_VALUE) {
                 extraSpace = 0 ;
             }
             extraSpace = extraSpace - 1 ;
                     if (extraSpace > 0)
                      { tok.preSpace = tok.preSpace + 
                           Parameters.LaTeXLeftSpace(extraSpace) ; };

           }  // END then OF if (tok.belowAlign != -1)
      if (tok.aboveAlign.line == -1)
           { /**************************************************************
             * tok not aligned.                                            *
             **************************************************************/
             float savedPreSpace = tok.preSpace;
             if (pc.item == 0)
               { /**********************************************************
                 * Left-most token on the line.                            *
                 **********************************************************/
                 tok.preSpace = Parameters.LaTeXLeftSpace(tok.column);
               }
             else
               { if (   (pc.item == 1)
                     && (spec[pc.line][0].type == Token.COMMENT))
                   { /******************************************************
                     * Left-most non-left-comment token on the line.       *
                     ******************************************************/
                     tok.preSpace = Parameters.LaTeXLeftSpace(tok.column)
                                      - spec[pc.line][0].preSpace;
                   }
                 else
                   { /******************************************************
                     * Add extra space for each extra space between this   *
                     * token and the one to its left.                      *
                     ******************************************************/
                     Token ltok = spec[pc.line][pc.item - 1] ;
                     int extraSpace = 
                          tok.column - (ltok.column + ltok.getWidth()) - 1;
                     if (extraSpace > 0)
                      { tok.preSpace = 
                           Parameters.LaTeXLeftSpace(extraSpace) ; };
                   }
               }
              if (tok.preSpace < savedPreSpace) {
                 tok.preSpace = savedPreSpace ;
              }
           }  // END  OF if (tok.belowAlign == -1)
       else
       { /******************************************************************
         * tok aligned with a previous token.                              *
         ******************************************************************/
         float savedPreSpace = tok.preSpace;
               tok.preSpace = 0;  // needed to keep TotalIndent from getting confused
         tok.preSpace =  
                TotalIndent(spec, tok.aboveAlign)
              - TotalIndent(spec, pc)
              + Parameters.LaTeXLeftSpace(
                 tok.column - tok.aboveAlign.toToken(spec).column) ;

         if (tok.preSpace < savedPreSpace) {
             tok.preSpace = savedPreSpace ;
         }
         /**************************************************************
         * If prespace is negative, then something funny has           *
         * happened.  So, we set it to zero.                           *
         **************************************************************/
         if (tok.preSpace < 0) { tok.preSpace = 0;};                  

       } // END else OF if (tok.aboveAlign == -1)
      nextPos = nextPos + 1;
    }; // END while (nextPos < posCols.length)
   
  }; // END public static void SetDimensions


  private static int findInt(String str, int start)
   /************************************************************************
   * Finds the Natural number represented by the string starting at        *
   * str.charAt(start).                                                    *
   ************************************************************************/
   { int nextChar = start;
     while (('0' <= str.charAt(nextChar) ) && (str.charAt(nextChar) <= '9'))
      { nextChar = nextChar + 1; };
     return Integer.parseInt(str.substring(start,nextChar));
   } ;

 
  private static float findFloat(String str, int start)
   /************************************************************************
   * Finds the float represented by the string starting at                 *
   * str.charAt(start).                                                    *
   ************************************************************************/
   { int nextChar = start;
     while (   (('0' <= str.charAt(nextChar) ) && (str.charAt(nextChar) <= '9'))
            || (str.charAt(nextChar) == '.'))
      { nextChar = nextChar + 1; };
     return Misc.stringToFloat(str.substring(start,nextChar));
   } ;

  private static float TotalIndent(Token[][] spec, Position pos)
    /***********************************************************************
    * The total indentation of the token tok at pos, according to the      *
    * current values of the preSpace and distFromMargin fields.  That      *
    * value equals tok.distFromMargin plus the sum of t.preSpace for all   *
    * tokens t to the left of or equal to tok.                             *
    ***********************************************************************/
    { float val = 0 ;
      int item = 0 ;
      while (item <= pos.item)
       { val = val + spec[pos.line][item].preSpace;
         item = item + 1;
       } ;
      return val + pos.toToken(spec).distFromMargin;
    }

  /**
   * Equals TotalIndent(spec, pos) plus the extra space added because of
   * spaces to the left of the token at pos
   * 
   * @param spec
   * @param pos
   * @return
   */
  private static float TotalIndentWithSpace(Token[][] spec, Position pos) {
      int posOfFirstSpaceToLeft = 0;
      if (pos.item > 0) {
          Token tokToLeft = spec[pos.line][pos.item-1] ;
          posOfFirstSpaceToLeft = tokToLeft.column + tokToLeft.getWidth();          
      }
      float spaceToLeft = Parameters.LaTeXLeftSpace(
                           pos.toToken(spec).column - posOfFirstSpaceToLeft - 1) ;
      return spaceToLeft + TotalIndent(spec, pos) ;
  }
  
  private static String FixString(String inputStr)
    /***********************************************************************
    * Result is Misc.TeXify(str) with spaces replaced by "\ " and "-"      *
    * replaced by {-}.                                                     *
    ***********************************************************************/
    { String result = "" ;
      String str = Misc.TeXify(inputStr);
      int pos = 0 ;
      while (pos < str.length())
       { char ch = str.charAt(pos) ;
         if (ch == ' ')
           { result = result + "\\ " ; }
         else 
           { if (ch == '-')
               { result = result + "{-}" ; }
             else
               { result = result + ch ; }
           } ;
         pos = pos + 1 ;
       } ;
      return result ;
    }    

  static String PfStepString(String str) 
    /***********************************************************************
    * Converts the string "<42>ab." to "\@pfstepnum{42}{ab.}"              *
    ***********************************************************************/
    { int leftAnglePos = str.indexOf('>') ;
      return Parameters.LaTeXPfStepNumCommand + "{" +
             str.substring(1, leftAnglePos) + "}{" +
             str.substring(leftAnglePos+1) + "}" ;
    }


/* ----------------------------------------------------------------------- */


public static void WriteLaTeXFile(Token[][] spec)
 { // BEGIN  WriteLaTeXFile(Token[][] spec)
  OutputFileWriter writer = 
         StartLaTeXOutput(Parameters.LaTeXOutputFile);
  InnerWriteLaTeXFile(spec, writer, true);
  writer.putLine("\\end{document}");
  writer.close(); 
  return ;
 }

public static void WriteTLATeXEnvironment(Token[][] spec, 
                                          OutputFileWriter writer)
 { writer.putLine("\\begin{tlatex}");
   InnerWriteLaTeXFile(spec, writer, false);
   writer.putLine("\\end{tlatex}");
 }

private static void InnerWriteLaTeXFile(Token[][] spec, 
                                        OutputFileWriter writer,
                                        boolean tlaMode)
  /*************************************************************************
  * Writes the body of the file (everything between the \begin{document}   *
  * and \end{document} for the WriteLaTeXFile method.  Also used to write  *
  * the body of a tlatex environment for the WriteTLATeXEnvironment        *
  * method.  It is called with the tlaMode flag true by WriteLaTeXFile     *
  * and with it false by WriteTLATeXEnvironment.                           *
  *************************************************************************/
 { // BEGIN  InnerWriteLaTeXFile(Token[][] spec)
  Vector commentVec = new Vector(150);
    /***********************************************************************
    * Used to hold the vector argument to FormatComments.WriteComment.     *
    ***********************************************************************/
  int line = 0 ;
      /*********************************************************************
      * line is the current line of the spec being ouput.                  *
      *********************************************************************/

// Debug.print2DArray(spec, "spec") ;

  /*************************************************************************
  * Skip leading blank lines.                                              *
  *************************************************************************/
  while (   (line < spec.length)
         && (   (spec[line] == null)
             || (spec[line].length == 0)))
   { line = line+1 ;}

  /*************************************************************************
  * Output the prolog, if there is one, and set line, item to the first    *
  * non-prolog token.                                                      *
  *************************************************************************/
  int item = 0 ;
  if (  (line < spec.length)
        && (spec[line][item].type == Token.PROLOG))
   {/***********************************************************************
    * Write the prolog as an unindented PAR comment.                       *
    *                                                                      *
    * First, set commentVec to the vector of prolog lines.                 *
    ***********************************************************************/
    boolean endProlog = false ;
    while (   ! endProlog 
              && (line < spec.length))
     {if  (   (spec[line] == null)
           || (spec[line].length == 0))
       { commentVec.addElement("");
         line = line + 1;
       } 
      else
       {if (spec[line][0].type != Token.PROLOG)
         {endProlog = true ;}
        else
         {commentVec.addElement(spec[line][0].string);
          if (spec[line].length > 1)
           /*********************************************************
           * If a prolog token is followed by a token on the same   *
           * line, then that token is not a prolog token.           *
           *********************************************************/
           {item = 1;
            endProlog = true ;
           }
          else
           {line = line + 1;
           } ;
         };
       };
     } ;                  // END while

    /***********************************************************************
    * Having accumulated the prolog in commentVec, we actually print it    *
    * (as a PAR comment) if the user hasn't specified the -noprolog        *
    * option.                                                              *
    ***********************************************************************/
    if (Parameters.PrintProlog)
      { FormatComments.WriteComment
              (writer, commentVec, FormatComments.PAR, 0, tlaMode);
      } ; 

   };                    // END if ((line < spec.length) ...)
  /***********************************************************************
  * End output prolog lines.                                             *
  ***********************************************************************/

  /***********************************************************************
  * If shading, then set LaTeX's shading flag.                           *
  ***********************************************************************/
  if (Parameters.CommentShading)
    {writer.putLine("\\setboolean{shading}{true}") ;}

  boolean inBeginModule = false ;
    /***********************************************************************
    * True iff we have output the first "----" of "---- MODULE foo ----"   *
    * but not the second.                                                  *
    ***********************************************************************/

  boolean done = false ;

  boolean inSub = false;
    /***********************************************************************
    * True while putting out sub/superscript tokens.                       *
    ***********************************************************************/
 
  boolean hasPcal = TokenizeSpec.hasPcal ;
  int pcalStartLine ;
  int pcalEndLine ;
  if (TokenizeSpec.hasPcal) {
    pcalStartLine = TokenizeSpec.pcalStart.line;
    pcalEndLine   = TokenizeSpec.pcalEnd.line;
  }
  else {
      pcalStartLine = Integer.MAX_VALUE ;
      pcalEndLine   = Integer.MAX_VALUE - 1;
  }
  /***********************************************************************
  * Write out the body and epilog of the specification.                  *
  ***********************************************************************/
  /*
   * pcalLine equals true during the processing of each line of the
   * PlusCalCode iff we are shading comments and hence PlusCal code.
   */
  boolean pcalLine = false;
  while (line < spec.length)
   { // BEGIN while (line < spec.length)

    if (tlaMode && TokenizeSpec.hasPcal) {
      boolean pcalLineNext = ( pcalStartLine <= line && line <= pcalEndLine) ;
      if (pcalLineNext && !pcalLine) {
          writer.putLine("\\pcalsymbolstrue") ;
          if (Parameters.CommentShading && ! Parameters.NoPlusCalShading) {
              writer.putLine("\\pcalshadingtrue") ;
          }
          if (TokenizeSpec.isCSyntax) {
              writer.putLine("\\csyntaxtrue") ;
          }
          else {
              writer.putLine("\\csyntaxfalse") ; 
          }
      }
      if (pcalLine && !pcalLineNext) {
          writer.putLine("\\pcalshadingfalse \\pcalsymbolsfalse") ;
      }
      pcalLine = pcalLineNext ;
    }
        
    if (spec[line].length == 0)
     {                   //  BEGIN then OF if (spec[line].length == 0)
       /********************************************************************
       * Skip over blank lines and write an appropriate \vspace command.   *
       ********************************************************************/
       int blankLines = 0 ;
       while (   (line < spec.length)
              && (spec[line].length == 0))
         { blankLines = blankLines + 1;
           line = line + 1;
         }
//       if (pcalLine) {
//           writer.putLine("\\begin{ppar}%") ;
//       }
       writer.putLine(
         //(  pcalLine2 ? "\\setlength{\\pcalvspace}{" :
        // "\\par\\vspace{" )
         "\\@pvspace{"
         + Misc.floatToString(Parameters.LaTeXVSpace(blankLines), 2) 
         + "pt}%" );
//       if (pcalLine) {
//           writer.putLine("\\end{ppar}%") ;
//       }


     }                   //  END then OF if (spec[line].length == 0)
       
    else
     {                   //  BEGIN else OF if (spec[line].length == 0)

      /*
       * Write "\begin{ppar}%" if this is a PlusCal Line.
       */
//      if (pcalLine) {
//          writer.putLine("\\begin{ppar}%") ;
//      }
      
      /********************************************************************
      * Write out the current line.                                       *
      ********************************************************************/
       Debug.Assert(spec[line].length != 0,
         "LaTeXOutput.WriteLaTeXFile: Unprocessed or unskipped blank line.");
      String outLine = "" ;
  
      boolean openLine = false ;
        /*******************************************************************
        * True iff there is an open LaTeXStartLine or LaTeXContinueLine    *
        * command.                                                         *
        *******************************************************************/
  
  
      boolean issueVSpace = false ;
         /********************************************************************
         * Will be set true if this line and perhaps some following ones     *
         * should be replaced by a LaTeXEndMultiLineVSpace command.          *
         ********************************************************************/
         
      if (   (spec[line][0].type == Token.COMMENT)
          && (   ( ((CommentToken) spec[line][0]).subtype 
                      == CommentToken.MULTI               )
              || ( ((CommentToken) spec[line][0]).subtype 
                      == CommentToken.NULL)               ) )
  
       { // BEGIN if ( (spec[line][0].type == Token.COMMENT) ... )
        /***************************************************************
        * Inside a multi-line comment that starts the line.  If all    *
        * the remaining tokens of the comment start their lines, then  *
        * we must issue a LaTeXEndMultiLineVSpace command.  Note that  *
        * the tokens forming a multi-line comment are doubly-linked    *
        * by belowAlign and aboveAlign pointers.                       *
        ***************************************************************/
        issueVSpace = true ;
        int i = line ;
        boolean endSearch = false ;
        while (   issueVSpace 
               && ( ! endSearch)
               && ( i < spec.length))
         /**************************************************************
         * Invariant: All lines from line through i begin with the     *
         * same multi-line comment.                                    *
         **************************************************************/
         {
          Token bATok = null;
          if (spec[i][0].belowAlign.line != -1)
            { bATok = spec[i][0].belowAlign.toToken(spec) ; } ;
          if (   (spec[i][0].belowAlign.line == -1)
              || (bATok.type != Token.COMMENT)
                   /****************************************************
                   * I think this disjunct should never be true.       *
                   ****************************************************/
              || (   (((CommentToken) bATok).subtype != CommentToken.MULTI)
                  && (((CommentToken) bATok).subtype != CommentToken.NULL)))
           { endSearch = true ;
           }
          else
           { if (spec[i][0].belowAlign.item != 0)
              { issueVSpace = false ;
                endSearch = true ;
              } 
            else
             { i = i + 1;
             };
            } ;
         }; // END while ( issueVSpace ... )
  
       if (issueVSpace)
        { // BEGIN if (issueVSpace)
          /*****************************************************************
          * Have to replace lines line through i by a                      *
          * LaTeXEndMultiLineVSpace command whose argument is the number   *
          * of lines above line in the same comment.                       *
          *****************************************************************/
          int count = line - spec[line][0].aboveAlign.line ;
          writer.putLine(Parameters.LaTeXEndMultiLineVSpace + "{" 
                      + count + "}%");
          line = i ;
          outLine = "";
          openLine = false ;
        }; // END if (issueVSpace)
  
       }; // END if ( (spec[line][0].type == Token.COMMENT) ... )
      if (! issueVSpace)
       { // BEGIN if (! issueVSpace)
  
        /*********************************************************************
        * Start the output line with a LaTeXStartLine command.               *
        *********************************************************************/
        outLine = Parameters.LaTeXStartLine + "{" ; 
//        if (pcalLine2) {
//            outLine = "\\xtest{" ;
//        }
        openLine = true ;

        /*******************************************************************
        * If numbering, then write the line number.                        *
        *******************************************************************/
        if (Parameters.PrintLineNumbers)
          { outLine = outLine 
                      + "\\makebox[0pt][r]{\\scriptsize "
                      + (line + 1) + "\\hspace{1em}}";
          };

        /********************************************************************
        * Append to outLine the output for the tokens on the line.          *
        ********************************************************************/
        while (  (! done) 
              && (item < spec[line].length) )
         { // BEGIN while (   (! done) && (item < spec[line].length)  )
          /*******************************************************************
          * Assertion: outLine has an open LaTeXStartLine or                 *
          * LaTeXContinueLine command.                                       *
          *******************************************************************/
          Debug.Assert(openLine,
               "LaTeXOutput.WriteLaTeXFile: prematurely closed line");
  
          /*****************************************************************
          * Process the current item.                                      *
          *****************************************************************/
          Token tok = spec[line][item] ;
          Position pos = new Position(line, item);
            /***************************************************************
            * The current token and its position.                          *
            ***************************************************************/
  
          if (inSub && (! tok.subscript))
            { /*************************************************************
              * The current subcript has ended; close the command's "}".   *
              *************************************************************/
              inSub = false ;
              outLine = outLine + "}";
            } ;
               
          /*****************************************************************
          * Write the command to produce the preSpace space.               *
          *****************************************************************/
          if (tok.preSpace >= Misc.stringToFloat("0.01"))
            { outLine = outLine + Parameters.LaTeXSpaceCommand + "{"
                          + Misc.floatToString(tok.preSpace,2) + "}";
            } ;
  
          switch (tok.type)
           { // BEGIN switch (tok.type)
             case Token.BUILTIN :
               int symType = BuiltInSymbols.GetBuiltInSymbol(
                                       spec[line][item].string, true).symbolType ;
                 if (   (! inSub)
                     && (   (symType == Symbol.SUBSCRIPTED)
                         || tok.string.equals("^"))
                     && (item + 1 < spec[line].length)
                     && spec[line][item+1].subscript )
                  { /*******************************************************
                    * This starts a sub or superscript.                    *
                    *******************************************************/
                    inSub = true ;
                    if (symType == Symbol.SUBSCRIPTED)
                     { /****************************************************
                       * It's a subscript.                                 *
                       ****************************************************/
                       outLine = outLine + " " +  
                          BuiltInSymbols.GetBuiltInSymbol(
                                                   tok.string, true).TeXString
                          + "_{";
                     }    
                    else
                     { /****************************************************
                       * It's a superscript.                               *
                       ****************************************************/
                       outLine = outLine + " " + "^{";
                     }    
                  } // END then OF if (   (! inSub) ... )
                 else
                  { outLine = outLine + " " +  
                     BuiltInSymbols.GetBuiltInSymbol(tok.string, true).TeXString;
                  }; // END else OF if (   (! inSub) ... )
               break ;
  
             case Token.NUMBER :
               /**************************************************************
               * A number can begin with a '\'.  Won't bother optimizing     *
               * for this special case of TeXify'ing.                        *
               **************************************************************/
               outLine = outLine + " " + Misc.TeXify(tok.string) ; 
               break ;
  
             case Token.IDENT :
               outLine = outLine + " " + Misc.TeXifyIdent(tok.string) ; 
               break ;

             case Token.PCAL_LABEL :
               outLine = outLine + " " + Misc.TeXifyPcalLabel(tok.string) ;
               break ;
               
             case Token.STRING :
               outLine = outLine + Parameters.LaTeXStringCommand + "{"  
                          + FixString(tok.string) + "}";
               break ;
  
             case Token.PF_STEP :
               outLine = outLine + PfStepString(tok.string) ;
               if ( ((Token.PfStepToken) tok).needsSpace )
                 {outLine = outLine + "\\ "; } ;
               break ;

             case Token.COMMENT :
               CommentToken ctok = (CommentToken) tok ;
  
               switch (ctok.subtype)
                { case CommentToken.ONE_LINE :
                    /*********************************************************
                    * Write out the line so far, closing the open            *
                    * LaTeXStartLine or LaTeXContinueLine command, and set   *
                    * outLine to the beginning of a LaTeXContinueLine        *
                    * command.                                               *
                    *********************************************************/

                    /*******************************************************
                    * We're going to call FormatComments.WriteComment to   *
                    * write out the comment, so we have to close the       *
                    * current LaTeXStartLine or LaTeXContinueLine command  *
                    * and write it out, setting outLine to "".             *
                    *******************************************************/
                    Misc.BreakStringOut(writer, outLine + "}%" ) ;
  
  
                    Vector vec = new Vector(2);
                    vec.addElement(tok.string) ;
                    if (   (item == 0)
                        && (spec[line].length > 1))
                      /*****************************************************
                      * If this is a left-comment, then typeset it with    *
                      * width zero.  Otherwise, format it as a one-line    *
                      * comment.  We need to format it as a one-line       *
                      * comment even if it's the only token on the line    *
                      * so the following case will align properly:         *
                      *                                                    *
                      *    xxx (* yyy *)                                   *
                      *        (* yyy *)                                   *
                      *****************************************************/
                      { FormatComments.WriteComment(writer, vec, 
                             FormatComments.ZERO_WIDTH, 0, tlaMode) ;
                      }
                    else
                      { FormatComments.WriteComment(writer, vec, 
                                FormatComments.ONE_LINE, 0, tlaMode) ;
                      }
  
                    /*********************************************************
                    * There may be more to come on the line, so open a       *
                    * LaTeXContinueLine command.                             *
                    *********************************************************/
                    outLine = Parameters.LaTeXContinueLine + "{" ;
                    break ;
  
                  case CommentToken.BEGIN_MULTI :
  
                    /*********************************************************
                    * The comment is going to be typeset so it goes to the   *
                    * right margin.  Set commentWidth to its width, in       *
                    * points.                                                *
                    *********************************************************/
                    float commentWidth = Parameters.LaTeXtextwidth  
                                           - TotalIndent(spec, pos); 
  
                    /*******************************************************
                    * Set mlineVector to the vector of non-NULL lines in   *
                    * the multi-line comment, and set lastLine to the      *
                    * last line of the comment, which may be the NULL      *
                    * line.  (A multi-line need not be ended by a NULL     *
                    * line.)                                               *
                    *******************************************************/
                    Vector mlineVector = new Vector();
                    Position nextPos = ctok.belowAlign;
                    boolean more = true;
                    Token ntok = null;
                    int lastLine = pos.line;
                    while (more && (nextPos.line != -1))
                     { ntok = nextPos.toToken(spec) ;
                       /****************************************************
                       * Change made 10 Nov 2001                           *
                       * I originally had                                  *
                       *                                                   *
                       *   Debug.Assert(ntok.type == Token.COMMENT,        *
                       *       "Non-comment part of multi-line comment."); *
                       *                                                   *
                       * here.  However, if the last line of a multi-line  *
                       * comment isn't a line of *'s, then it could be     *
                       * below-aligned with a non-comment.  So, I added    *
                       * the ntok.type==Token.COMMENT test to the          *
                       * following IF.                                     *
                       ****************************************************/
                       if (   (ntok.type == Token.COMMENT)
                           && (((CommentToken) ntok).subtype == 
                                   CommentToken.MULTI))
                         { mlineVector.addElement(ntok.string) ;
                           lastLine = nextPos.line ;
                           nextPos = ntok.belowAlign;
                         } 
                       else
                         { more = false;
                         } ;
                     } ;
                    if (   (nextPos.line != -1)
                        && (ntok.type == Token.COMMENT)
                        && (((CommentToken) ntok).subtype == CommentToken.NULL))
                      { lastLine = nextPos.line; 
                      } ;
  
                    /*******************************************************
                    * Set parMulti true iff there is no token to the left  *
                    * of any line in the multi-line comment.               *
                    *******************************************************/
                    boolean parMulti = true ;
                    Position cPos = pos ;
                    while ( parMulti && (cPos.line < lastLine) )
                     { parMulti = (cPos.item == 0) ;
                       cPos = cPos.toToken(spec).belowAlign ;
                     } ;
                    parMulti = parMulti && (cPos.item == 0) ;
  
                    /*******************************************************
                    * Write out the comment.                               *
                    *******************************************************/
                    if (parMulti)
                      { /***************************************************
                        * There's nothing to the left of this comment.     *
                        * Just delete the current LaTeXStartLine command   *
                        * and write out the comment as a PAR comment.      *
                        ***************************************************/
                       outLine = "" ;
                       openLine = false ;
                       FormatComments.WriteComment(writer, mlineVector,
                            FormatComments.PAR, TotalIndent(spec, pos), 
                            tlaMode);
                       line = lastLine ;
                      }
                    else
                      { /***************************************************
                        * There's something to the left of the comment.    *
                        * Write out the beginning of the line and then     *
                        * write the comment.                               *
                        ***************************************************/
                        Misc.BreakStringOut(writer, outLine + "}%" ) ;
                        outLine = "" ;
                        openLine = false ;
                        FormatComments.WriteComment(writer, mlineVector,
                             FormatComments.RIGHT_MULTI, commentWidth, 
                             tlaMode) ;
                      } ;
  
                    break ;
  
                  case CommentToken.NULL :
                  case CommentToken.MULTI :
                    /*******************************************************
                    * All subsequent lines of a multi-line comment were      *
                    * output with the BEGIN_MULTI line.  This is the last    *
                    * token on the line, so there's no need to open a        *
                    * LaTeXContinueLine command.                             *
                    *******************************************************/
                    break ;
  
                  case CommentToken.PAR :
                    /*******************************************************
                    * This is the only token on the line, so we can        *
                    * delete the LaTeXStartLine command.                   *
                    *******************************************************/
                    outLine = "" ;
                    openLine = false ;
                    
                    /*******************************************************
                    * Set lineVector to the vector of lines in the         *
                    * multi-line comment, and skip over all its lines.     *
                    *******************************************************/
                    Debug.Assert(outLine.equals(""),
                      "Non-empty outLine at beginning of PAR comment");
  
                    Vector lineVector = new Vector();

                    /*******************************************************
                    * Add tok.column + 2 spaces to beginning of first      *
                    * line.                                                *
                    *******************************************************/
                    String spaces = "  ";
                    int j = 0 ;
                    while (j < tok.column)
                      { spaces = spaces + " ";
                        j = j + 1;
                      } ;
                    
                    lineVector.addElement(spaces + tok.string) ;
                    while (   (line + 1 < spec.length)
                           && (   (spec[line + 1].length == 0)
                               || (   (spec[line + 1][0].type == 
                                          Token.COMMENT)
                                   && (((CommentToken) 
                                              spec[line + 1][0]).subtype 
                                         == CommentToken.PAR))))
  
                     { if (spec[line + 1].length == 0)
                         { lineVector.add("");}
                       else 
                         { lineVector.add(spec[line + 1][0].string);};
                       line = line + 1;
                     } ;
                    

                    /*******************************************************
                    * Write out lineVector.                                *
                    *******************************************************/
                    FormatComments.WriteComment
                       (writer, lineVector, FormatComments.PAR, -2, tlaMode) ;
  
                    break ;
  
                  default :
                  Debug.ReportBug(
                     "Bad comment token subtype at position (" 
                         + line + ", " + item + ")\n"
                    + "    in LaTeXOutput.WriteAlignmentFile");
  
                } ; // END switch (ctok.subtype)
               break ;
  
             case Token.DASHES :
               if (inBeginModule)
                { /*********************************************************
                  * Ending a "--- MODULE foo ---".                         *
                  *********************************************************/
                  outLine = outLine + "}" + Parameters.LaTeXRightDash 
                              + "{" ;
                  inBeginModule = false ;
                }  // END THEN if (inBeginModule)
               else
                { if (   (item + 1 < spec[line].length)
                       && (spec[line][item+1].string.equals("MODULE")))
                   { /******************************************************
                     * Starting a "--- MODULE foo ---".                    *
                     ******************************************************/
                     outLine = outLine + "}" + 
                                 Parameters.LaTeXLeftDash + "{" ;
                     inBeginModule = true ;
                   } // END THEN of if ( (item + 1 < ... ))
                  else
                   { /******************************************************
                     * This is a mid-module dash.                          *
                     ******************************************************/
                     outLine = outLine + "}" + Parameters.LaTeXDash 
                                   + "{" ;
                   } // END ELSE of if ( (item + 1 < ... ))
  
                } ; // END ELSE if (inBeginModule)
               break ;
  
             case Token.END_MODULE :
               outLine = outLine + "}" + Parameters.LaTeXEndModule 
                           + "{" ;
               break ;
  
             case Token.EPILOG :
               /************************************************************
               * The epilog is written as an unshaded PAR comment.         *
               ************************************************************/

               /************************************************************
               * If there has been other output for this line, we must     *
               * close the LaTeXStartLine or LaTeXContinueLine command     *
               * and write out the line.  Otherwise, we just delete the    *
               * LaTeXStartLine command.                                   *
               ************************************************************/
               if (item != 0)
                { Misc.BreakStringOut(writer, outLine + "}%");
                  line = line + 1;
                    /*******************************************************
                    * We throw away an EPILOG token to the right of the    *
                    * "======" that ends the module.  It doesn't seem to   *
                    * be worth the effort of figuring out what to do with  *
                    * it, and it's highly unlikely that someone            *
                    * intentionally typed something on the same line as    *
                    * the "=====".  The extra token probably consists      *
                    * only of spaces.                                      *
                    *******************************************************/
                } ;
               outLine = null ;
               openLine = false;

               if (Parameters.PrintEpilog)
                 { writer.putLine("\\setboolean{shading}{false}");
                     /******************************************************
                     * Turn off shading for the epilog.                    *
                     ******************************************************/
  
                   /********************************************************
                   * Print the epilog like a PAR comment.                  *
                   ********************************************************/
                   Vector lineVector = new Vector() ;
                   while (line < spec.length)
                    { if (spec[line].length == 0)
                       { lineVector.addElement(""); }
                      else
                       { lineVector.addElement(spec[line][0].string);};
                      line = line + 1;
                    } ;
  
                   FormatComments.WriteComment
                     (writer, lineVector, FormatComments.PAR, 0, tlaMode);
                 }
               done = true ;
               break ;
  
             default :
               Debug.ReportBug(
                    "Bad token type at position (" + line + ", " 
                         + item + ")\n"
                  + "    in LaTeXOutput.WriteLaTeXFile");
           };  // END switch (tok.type)
  
          item = item + 1 ;
         };                // END while ((! done) && (item < spec[line].length))
       };                 // END if (! issueVSpace)
  
      if (inSub) 
       { /*****************************************************************
         * If inside a sub/superscript, have to close the "^{" or "_{".   *
         *****************************************************************/
         Debug.Assert(outLine != null,
                         "Unclosed sub/superscript command at end of line") ;
         outLine = outLine + "}";
         inSub = false ;
       };         
  
      if (openLine)
       /******************************************************************
       * openLine has been set to false if the line has already been     *
       * written out.                                                    *
       ******************************************************************/
       { Misc.BreakStringOut(writer, outLine + "}%");
       } ;
      
       /*
        * Write "\end{ppar}%" if this is a PlusCal Line.
        */
//       if (pcalLine) {
//           writer.putLine("\\end{ppar}%") ;
//       }

      outLine = "" ;
      item = 0 ;
      line = line + 1;
     }                 // END else OF if (spec[line].length == 0)
    
   };                // END while (line < spec.length)
} ;

protected static String prependMetaDirToFileName(String fileName) {
    String outputFileName = fileName;
    if (! Parameters.MetaDir.equals("")) {
        outputFileName = Parameters.MetaDir + File.separator + outputFileName;
    }
ToolIO.out.println("looking for file: " + outputFileName);
    return outputFileName;
}
	
}

/* last modified on Wed 19 Sep 2007 at  6:15:07 PST by lamport */
