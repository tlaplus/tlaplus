// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS Parameters                                                         *
*                                                                          *
* The fields of this class consist of all the parameters used by           *
* TLATeX.  Some of them are set by program options.                        *
***************************************************************************/
package tla2tex;

import java.io.File;

public final class Parameters
{ 

  /*************************************************************************
  * Parameters Related to non-file Options                                 *
  *************************************************************************/
  
  public static boolean Debug = false ;
    /***********************************************************************
    * True if the -debug option is chosen.  At the moment, this just       *
    * causes timing information to be output.                              *
    ***********************************************************************/

  public static boolean TLAOut = false ;
    /***********************************************************************
    * True if the -tlaOut option is chosen.                                *
    ***********************************************************************/
  
  public static String TLAOutFile = "" ;
    /***********************************************************************
    * If the -tlaOut option is present, this is the file it specified.     *
    ***********************************************************************/

  public static boolean TLACommentOption = false ;
    /***********************************************************************
    * True if the -tlaComment option is chosen.                            *
    ***********************************************************************/
    
  public static boolean CommentShading = false ;
  /***********************************************************************
  * True if comments are to be shaded in the output.                     *
  ***********************************************************************/
  
  public static boolean NoPlusCalShading = false ;
  /***********************************************************************
  * True if PlusCal code should not be shaded when CommentShading is     *
  * true; meaningless otherwise.                                         *
  ***********************************************************************/
  
  public static boolean PrintProlog = true ;
    /***********************************************************************
    * True unless the -noProlog option is specified.  It determines        *
    * whether the prolog of a module (the part that appears before the     *
    * start of the module) is to be printed.                               *
    ***********************************************************************/

  public static boolean PrintEpilog = true ;
    /***********************************************************************
    * True unless the -noEpilog option is specified.  It determines        *
    * whether the epilog of a module (the part that appears after the end  *
    * of the module) is to be printed.                                     *
    ***********************************************************************/

  public static boolean PrintLineNumbers = false ;
    /***********************************************************************
    * True iff the -number option is chosen.  It determines whether the    *
    * output will print line numbers.                                      *
    ***********************************************************************/
    
  public static float PSGrayLevel = Misc.stringToFloat(".85");
    /***********************************************************************
    * The gray level of shaded comment boxes, where 0 is black and 1 is    *
    * white.  Set by the -grayLevel option.                                *
    ***********************************************************************/
    
  public static String PSCommand = "dvips" ;
    /***********************************************************************
    * The command used to create a Postscript or pdf output file.          *
    * Set by -psCommand.                                                   *
    ***********************************************************************/
    
  public static boolean PSOutput = false ;
    /***********************************************************************
    * True iff creating Postscript output file.                            *
    ***********************************************************************/
   
  /*************************************************************************
  * File parameters.                                                       *
  *************************************************************************/

  public static String WordFile = "words.all" ;
    /***********************************************************************
    * The name of the resource file containing the list of all common      *
    * English words.  This file must contain one word per line, with no    *
    * spaces.                                                              *
    ***********************************************************************/
    
  public static String LaTeXStyleFile = "tlatex.sty" ;
    /***********************************************************************
    * The style file that defines the commands used in the LaTeX output    *
    * files.  It is read in and added to the output files, so it           *
    * shouldn't use "@" in command names without an explicit               *
    * \makeatletter command.                                               *
    ***********************************************************************/

  public static String UserStyleFile = "";
    /***********************************************************************
    * If not equal to "", then it is the user-supplied package that is     *
    * used instead of LaTeXStyleFile.  Set by the -style option.           *
    ***********************************************************************/
    
  public static final String HelpFile = "help.txt";
    /***********************************************************************
    * The file containing the -help message for tlatex.TLA.                *
    ***********************************************************************/

  public static final String InfoFile = "info.txt";
    /***********************************************************************
    * The file containing the -info message for tlatex.TLA, which is more  *
    * complete than the -help message.                                     *
    ***********************************************************************/

  public static final String TeXHelpFile = "texhelp.txt";
  public static final String TeXInfoFile = "texinfo.txt";
    /***********************************************************************
    * The corresponding files for tlatex.TeX                               *
    ***********************************************************************/
    
  public static String TLAInputFile = "" ;
    /***********************************************************************
    * The name of the input file.  It is set to equal the argument with    *
    * which the program is called.  If no extension is specified, then     *
    * ".tla" added if for tlatex.TLA, and ".tex" is added for tlatex.TeX.  *
    ***********************************************************************/
    
  public static String LaTeXOutputFile = "" ;
    /***********************************************************************
    * The name of the LaTeX output file (minus the ".tex" extension) used  *
    * to typeset the spec.  It is set by the -out option; the default      *
    * value is set by the GetArguments method (of class TLA or TeX).       *
    ***********************************************************************/

  public static String LaTeXAlignmentFile = "" ;
    /***********************************************************************
    * The name of the output file (minus the ".tex" extension) used to     *
    * write the alignment output--the LaTeX file that is executed to find  *
    * the widths of the typeset output for computing alignment spacing.    *
    * It is set by the -alignOut option; the default value is set by       *
    * TLA.GetArguments.                                                    *
    ***********************************************************************/

  public static String MetaDir = "" ;

  public static String LatexOutputExt = "dvi" ;

  /*************************************************************************
  * Parameters Related to TLATeX's LaTeX-Source Input                      *
  *************************************************************************/

  public static File ParentDir = null ;
  
  public final static int MaxOutputLineLength = 78  ;
    /***********************************************************************
    * The maximum number of characters in a line of the LaTeX input files  *
    * created by TLATeX.                                                   *
    ***********************************************************************/

  public static String LaTeXCommand = "latex" ;
    /***********************************************************************
    * The command used to run LaTeX.  Set by the -latexCommand option.     *
    ***********************************************************************/
    
  public static int LaTeXptSize = 10 ;
    /***********************************************************************
    * The point-size of type to use.  Must be 10, 11, or 12.               *
    ***********************************************************************/

  public static int LaTeXtextwidth = 360 ;
    /***********************************************************************
    * The value, in points, of \textwidth for the LaTeX files.  Set by     *
    * the -textwidth option.                                               *
    ***********************************************************************/

  public static int LaTeXtextheight = 541 ;
    /***********************************************************************
    * The value, in points, of \textheight for the LaTeX files.  Set by    *
    * the -textheight option.                                              *
    ***********************************************************************/

  public static int LaTeXhoffset = 0 ;
    /***********************************************************************
    * The value, in points, of a quantity added to TeX's \hoffset          *
    * parameter.  Useful for horizontally centering the output on the      *
    * page.  Set by the -hoffset option.                                   *
    ***********************************************************************/

  public static int LaTeXvoffset = 0 ;
    /***********************************************************************
    * The value, in points, of a quantity added to TeX's \hoffset          *
    * parameter.  Useful for centering the output vertically on the page.  *
    * Set by the -voffset option.                                          *
    ***********************************************************************/

  /*************************************************************************
  * Various LaTeX commands and environments used in the LaTeX output.      *
  *************************************************************************/

  public final static float LaTeXLeftSpace(int n)
    /***********************************************************************
    * The amount of space, in points, that corresponds to n spaces in the  *
    * input file.  The definition of \PROVE in tlatex.sty depends on this  *
    * method and needs to be changed if the method changes.                *
    ***********************************************************************/
    { return Misc.stringToFloat("4.1") * n * LaTeXptSize / 10  ; }
    
  public final static float LaTeXCommentLeftSpace(int n)
    /***********************************************************************
    * The amount of space, in points, that corresponds to n spaces in a    *
    * comment in the input file.                                           *
    ***********************************************************************/
    { return Misc.stringToFloat("2.5") * n * LaTeXptSize / 10 ; }

  public final static float LaTeXVSpace(int n)
    /***********************************************************************
    * The amount of vertical space, in points, that corresponds to n       *
    * blank lines in the input file.                                       *
    ***********************************************************************/
    { return Misc.stringToFloat("8.0") * n  ; }
    
  public final static float LaTeXCommentVSpace(int n)
    /***********************************************************************
    * The amount of space, in points, that corresponds to n blank lines    *
    * in a comment in the input file.                                      *
    ***********************************************************************/
    { return Misc.stringToFloat("5.0") * n ; }

  public final static String LaTeXCommentVSpaceCmd = "\\vshade";
    /***********************************************************************
    * A command that takes an argument n and creates an n-point vertical   *
    * space between paragraphs in a comment, with proper shading.  (A      *
    * simple \vspace command would leave unshaded white space between the  *
    * paragraphs when shading.)                                            *
    ***********************************************************************/
    
  public final static String LaTeXStartLine = "\\@x";  
    /***********************************************************************
    * The command \@x{txt} starts a specification line in the -out file    *
    * that begins with txt.                                                *
    ***********************************************************************/

  public final static String LaTeXContinueLine = "\\@xx";  
    /***********************************************************************
    * The command \@xx{txt} continues a specification line of the -out or   *
    * -alignOut file with text txt.                                        *
    ***********************************************************************/

  public final static String LaTeXStartAlignLine = "\\fl";  
    /***********************************************************************
    * The command \fl{txt} starts a specification line in the -alignOut    *
    * file that begins with txt.                                           *
    ***********************************************************************/

  public final static String LaTeXAlignPoint = "\\al" ;  
    /***********************************************************************
    * The command \al{i}{j}{txt} is put in the alignment file if item j    *
    * of line i is an alignment point, with txt the following text on the  *
    * specification line.  It puts "%{i}{j}{wd}" in the alignment file,    *
    * where wd is the width of the line up to that point,                  *
    ***********************************************************************/
    
  public final static String LaTeXStringCommand  = "\\@w" ;  
    /***********************************************************************
    * The command \@w{xyz} produces "xyz", formatted as a TLA+ string.     *
    ***********************************************************************/

  public final static String LaTeXPfStepNumCommand  = "\\@pfstepnum" ;  
    /***********************************************************************
    * The command \@pfstepnum{<42>}{1a.} produces "<42>1a.", properly      *
    * formatted with space after it.                                       *
    ***********************************************************************/
    
  public final static String LaTeXSpaceCommand  = "\\@s" ;  
    /***********************************************************************
    * The command \@s{n} produces an n-point horizontal space.              *
    ***********************************************************************/
    
  public final static String LaTeXOneLineCommentCommand = "\\@y" ;  
  public final static String LaTeXZeroWidthCommentCommand = "\\@z" ;  


  public final static String LaTeXLeftDash  = "\\moduleLeftDash\\@xx" ;  
  public final static String LaTeXRightDash = "\\moduleRightDash\\@xx" ;
    /***********************************************************************
    * The LaTeX commands that make the dashes to the left and right in     *
    * the beginning of a module.                                           *
    ***********************************************************************/
  public final static String LaTeXDash      = "\\midbar\\@xx" ;  
    /***********************************************************************
    * The LaTeX commands that make the decorative horizontal bar in the    *
    * middle of a module, which appears as a sequence of dashes in the     *
    * input.                                                               *
    ***********************************************************************/
  public final static String LaTeXEndModule = "\\bottombar\\@xx" ;  
    /***********************************************************************
    * The LaTeX commands that make the module-ending horizontal bar.       *
    ***********************************************************************/
    
  public final static String LaTeXAlignLeftDash  = "\\moduleLeftDash\\cl" ;  
  public final static String LaTeXAlignRightDash = "\\moduleRightDash\\cl" ;
  public final static String LaTeXAlignDash      = "\\midbar\\cl" ;  
  public final static String LaTeXAlignEndModule = "\\bottombar\\cl" ;  
    /***********************************************************************
    * These are the same as the four previous parameters, except they are  *
    * the commands for the alignment file.                                 *
    ***********************************************************************/
    
    
  public final static String LaTeXCommentPar = "cpar" ;  
    /***********************************************************************
    * This LaTeX environment takes two arguments--a dimension d in points  *
    * and a label.  It produces a sequence of paragraphs, shaped as        *
    * follows, where [label] is the result of typesetting the label        *
    * argument in an LR box.                                               *
    *                                                                      *
    *      left |<-- d -->[label]XXXXXXXXXXXXXXX                           *
    *    margin |                XXXXXXXXXXXXXXX                           *
    *           |                XXXXXXXXXXXXXXX                           *
    *           |                                                          *
    *           |                XXXXXXXXXXXXXXX                           *
    *           |                XXXXXXXXXXXXXXX                           *
    *                                                                      *
    * However, this environment should leave no vertical space above or    *
    * below it, or between its paragraphs.  (TLATeX inserts the proper     *
    * amount of vertical space.)                                           *
    ***********************************************************************/

    
  public final static String LaTeXRightMultiLineComment = "mcom" ;
    /***********************************************************************
    * The environment that formats a multi-line comment at the end of a    *
    * line.  It takes a single argument, the width of the comment in       *
    * points.  It works in conjunction with the LaTeXEndMultiLineVSpace    *
    * command.  The actual text inside it must all be in LaTeXCommentPar   *
    * environments.                                                        *
    ***********************************************************************/

  public final static String LaTeXLeftMultiLineComment = "lcom" ;
    /***********************************************************************
    * The environment that formats a multi-line comment with nothing to    *
    * its left.  It takes a single argument, the indentation in points of  *
    * the comment's left margin from the document's left margin.  The      *
    * actual text inside it must all be in LaTeXCommentPar environments.   *
    ***********************************************************************/

  public final static String LaTeXEndMultiLineVSpace = "\\multivspace" ;
    /***********************************************************************
    * The command to produce vertical space indicated by "|"s in this      *
    * situation                                                            *
    *                                                                      *
    *     xxxx (*************)                                             *
    *     xxxx (* ccccccccc *)                                             *
    *      |   (* ccccccccc *)                                             *
    *      |   (* ccccccccc *)                                             *
    *      |   (* ccccccccc *)                                             *
    *      |   (*************)                                             *
    *                                                                      *
    * where the argument is one less than the number of "xxxx" lines.      *
    * This command must immediately follow the LaTeXRightMultiLineComment  *
    * environment that produces the comment.                               *
    ***********************************************************************/
 }  

/* last modified on Wed 19 Sep 2007 at  4:53:41 PST by lamport */
