// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS Parameters                                                         *
*                                                                          *
* The fields of this class consist of all the parameters used by           *
* TLATeX.  Some of them are set by program options.                        *
***************************************************************************/
package unicasc;

public final class Parameters { 
  public static boolean Debug = false ;
  	// True if the -debug option is chosen.

  public static boolean TLAOut = false ;
    // True if the -tlaOut option is chosen.
  
  public static String TLAOutFile = "" ;
    // If the -tlaOut option is present, this is the file it specified.
   
  public static final String HelpFile = "help.txt";
    // The file containing the -help message for tlatex.TLA.

  public static final String InfoFile = "info.txt";
    /***********************************************************************
    * The file containing the -info message for tlatex.TLA, which is more  *
    * complete than the -help message.                                     *
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

  public static String MetaDir = "" ;
}  
