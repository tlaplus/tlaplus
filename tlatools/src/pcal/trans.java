package pcal;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Vector;

import pcal.MappingObject.Break;
import pcal.exception.FileToStringVectorException;
import pcal.exception.ParseAlgorithmException;
import pcal.exception.PcalResourceFileReaderException;
import pcal.exception.RemoveNameConflictsException;
import pcal.exception.StringVectorToFileException;
import pcal.exception.TLCTranslationException;
import pcal.exception.UnrecoverableException;
import tla2tex.Debug;
import util.ToolIO;

/***************************************************************************
* <pre>
* CLASS trans                                                              *
*                                                                          *
*  BUGS:                                                                   *
*     Accepts if (...) {...} ; else {...}                                  *
*     Generates code as if the ";" were not there.                         *
* -----------------------------------------------------------------        *
* History:                                                                 *
*   Version 1.0: Original release.                                         *
*                                                                          *
*   Version 1.1: (March 2006)                                              *
*                Introduced ability to have the translator                 *
*                add missing labels.                                       *
*                                                                          *
*   Version 1.2: (August 2007)                                             *
*                Introduced defaultInitValue so liveness can be            *
*                checked even with "uninitialized" variables.              *
*                                                                          *
*   Version 1.3: (February 2008)                                           *
*                Added "await" as a synonym for "when"                     *
*                                                                          *
*   Version 1.4: (June 2010)                                               *
*                Added the options statement and the -lineWidth option.    *
*                                                                          *               
*   Version 1.5: (Jan 2011)                                                *
*                 1. Added the -noDoneDisjunct option.                     *
*                 2. Added the new way of specifying fairness, with        *
*                    the "fair" keyword with "+" modifier, and the "+"     *
*                    and "-" label modifiers.                              *
*                 3. Automatically removes the stuttering-on-termination   *
*                    disjunction if all processes are "while (TRUE)"       *
*                    statements with no gotos to "Done".                   *
*                 4. In addition, if the "while (TRUE)"s have no           *
*                    internal labels, it removes the pc variable.          *
*                 5. Changed the representation of Process and Procedure   *
*                    nodes in the abstract syntax tree produced by         *
*                    the -writeAST option and used when TLC is producing   *
*                    the translation.                                      *
*                 The changes 3-5 are not implemented when the -version    *
*                 option specifies an earlier version.                     *
*                                                                          *
*   Version 1.6: (July 2011)                                               *
*                 - Added the "--fair algorithm" syntax for specifying     *
*                   weak fairness of the next-state action. (This          *
*                   changes the way fairness of a uniprocess algorithm was *
*                   specified in Version 1.5.  All legal Version 1.5       *
*                   algorithms should work with the "version 1.5" option.) *
*                 - Permitted previously defined macros to be called       *
*                   inside a macro definition.                             *
*                                                                          *
*   Version 1.7: (19 January 2012)                                         *
*                 - Translator adds "BEGIN/END TRANSLATION" if needed.     *
*                 - Added support for Toolbox Goto PCal Source command.    *
*                                                                          *
*   Version 1.8: (30 Mar 2012)                                             *
*                 - Changed translation to remove stuttering-on-           *
*                   termination disjunction if some process is             *
*                   "while (TRUE)".                                        *
*                 - Omitted the Termination definition if the stuttering-  *
*                   on-termination disjunction is removed, since that      *
*                   implies Termination is always FALSE.                   *
*                (4 May 2012)                                              *
*                 - Removed the unnecessary CASE in the pc = ... clause of *
*                   the Init predicate when there is only a single process *
*                   statement.                                             *
* -----------------------------------------------------------------        *
*                                                                          *
* This is the main method of the +CAL to TLA+ translation program.         *
* the program has the following command-line options. Only the ones        *
* marked with ** besides them can be specified in the file's               *
* options statement.  The "-" can be omitted when the option is in         *
* the options statement.                                                   *
*                                                                          *
*   -help  : Type a help file instead of running the program.              *
*                                                                          *
*   -spec name : Uses TLC and the TLA+ specification name.tla to do        *
*                the translation.  The files name.tla and name.cfg         *
*                are copied from the java/ directory to the current        *
*                directory; the file AST.tla that defines `fairness'       *
*                to equal the fairness option and `ast' to equal           *
*                the the AST data structure representing the algorithm     *
*                is written to the current directory; and TLC is run       *
*                on name.tla to produce the translation.                   *
*                                                                          *
*   -myspec name : Like -spec, except it finds the files names.tla         *
*                  and names.cfg in the current directory, instead         *
*                  of writing them there.                                  *
*                                                                          *
*   -spec2   name                                                          *
*   -myspec2 name : Like -spec and -myspec, except they use TLC2           *
*                   instead of TLC (aka TLC1).                             *
*                                                                          *
*   -writeAST : Writes the AST file as in the -spec option, but does       *
*               not perform the translation.                               *
*                                                                          *
*   -debug : Run in debugging mode, whatever that means.  For the          *
*            parser, it just means that the toString() methods             *
*            output the line and column number along with the              *
*            node.                                                         *
*                                                                          *
*   -unixEOL : Forces the use of Unix end-of-line convention, regardless   *
*              of the system's default.  Without this, when run on         *
*              Windows, the files it writes seem to have a "^M" at the     *
*              end of every line when viewed with Emacs.                   *
*                                                                          *
*** -wf : Conjoin to formula Spec weak fairness of each process's          *
*         next-state action                                                *
*                                                                          *
*** -sf : Conjoin to formula Spec strong fairness of each process's        *
*         next-state action                                                *
*                                                                          *
*** -wfNext : Conjoin to formula Spec weak fairness of the entire          *
*             next-state action                                            *
*                                                                          *
*** -nof : Conjoin no fairness formula to Spec.  This is the default,      *
*          except when the -termination option is chosen.                  *
*                                                                          *
*** -termination : Add to the .cfg file the command                        *
*                     PROPERTY Termination                                 *
*                  With this option, the default fairness option           *
*                  becomes -wf.                                            *
*                                                                          *
*   -nocfg : Suppress writing of the .cfg file.                            *
*                                                                          *
*** -noDoneDisjunct : Suppress the disjunct of the next-state              *
*                     relation that describes stuttering steps taken       *
*                     when the algorithm has halted.                       *
*                                                                          *
*** -label : Tells the translator to add missing labels.  This is          *
*            the default only for a uniprocess algorithm in which          *
*            the user has typed no labels.                                 *
*                                                                          *
*   -reportLabels : True if the translator should print the names          *
*                   and locations of all labels it adds.  Like             *
*                   -label, it tells the translator to add missing         *
*                   labels.                                                *
*                                                                          *
*** -labelRoot name : If the translator adds missing labels, it            *
*                     names them name1, name2, etc.  Default value         *
*                     is "Lbl_".                                           *
*                                                                          *
*  THE FOLLOWING OPTION ADDED IN VERSION 1.31                              *
*                                                                          *
*** -lineWidth : The translation tries to perform the translation so       *
*                lines have this maximum width.  (It will often            *
*                fail.)  Default is 78, minimum value is 60.               *
*                                                                          *
*  THE FOLLOWING OPTIONS ADDED IN VERSION 1.4                              *
*                                                                          *
*** -lineWidth : The translation tries to perform the translation so       *
*                lines have this maximum width.  (It will often            *
*                fail.)  Default is 78, minimum value is 60.               *
*                                                                          *
*** -version : The version of PlusCal for which this algorithm is          *
*              written.  If the language is ever changed to make           *
*              algorithms written for earlier versions no longer           *
*              legal, then the translator should do the appropriate        *
*              thing when the earlier version number is specified.         *
* ------------------------------------------------------------------------ *
*                                                                          *
* The program uses vector objects from the Vector class to implement       *
* sequences (lists).  This generates a compiler warning.                   *
*                                                                          *
* In Java data structures like arrays and Vectors, numbering starts with   *
* 0.  Unlike programmers, human beings count from 1.  I use the term "Java *
* ordinal" to refer a number that denotes a position that represents the   *
* first item as 0, and the term "human ordinal" to refer to an ordinary    *
* ordinal that counts the first item as 1.                                 *
*                                                                          *
*                                                                          *
* NOTE:                                                                    *
*                                                                          *
* One process should be able to read the pc or stack of another.  There    *
* is no logical reason to forbid this.  However, the definition of         *
* Translation in PlusCal.tla does not distinguish between instances of pc  *
* in the original algorithm and ones inserted by the translation.  The     *
* latter instances must be subscripted--that is replaced by something      *
* like pc[self].  Therefore, the Translation operator subscripts the       *
* instances of pc from the original algorithm.  The Java Translate method  *
* must not do this, but must subscript (and prime) only the instances of   *
* pc and stack introduced during the translation process.                  *
*                                                                          *
*                                                                          *
* The following bugs should all have been fixed by the addition of         *
* ParseAlgorithm.Uncommment by LL on 18 Feb 2006.                          *
*                                                                          *
*  - There cannot be a comment between a label and the                     *
*    following ":".                                                        *
*                                                                          *
*  - There cannot be a comment immediately before the ")" that ends        *
*    the list of arguments in a call statement.                            *
*                                                                          *
*  - The code for reporting the location of an error has the               *
*    following problem.  If the token where the error occurs is            *
*    preceded by a comment, then the position reported is that of the      *
*    beginning of the comment rather than that of the token.               *
*                                                                          *
* TENTATIVE CHANGE MADE                                                    *
*                                                                          *
* The following change was made along with a modification to the parser    *
* to allow semi-colons to be omitted when they're obviously unnecessary.   *
*                                                                          *
* The parser does not parse expressions in the +CAL algorithm; it just     *
* scans ahead to the first token that it can determine is not part of the  *
* expression.  To make this work, the following tokens that are legal in   *
* a TLA+ expression are illegal in a +CAL expression:                      *
*                                                                          *
*   variable   variables   begin   do   then   :=   ||                     *
*                                                                          *
* Making additional tokens illegal might help the parser find errors       *
* sooner.  For example,  example, if one forgets the ";" and writes        *
*                                                                          *
*        x := x + 1                                                        *
*       if x > y + 17 then ...                                             *
*                                                                          *
* the parser takes everything up to the "then" to be the right-hand side   *
* of the "x :=" assignment.  Making "if" illegal in an expression would    *
* allow the parser to catch the error at the "if".                         *
* </pre>
***************************************************************************/
class trans
{
    /** Status indicating no errors and successful process */
    static final int STATUS_OK = 1;
    /** Status of no errors, but abort of the translation */
    private static final int STATUS_EXIT_WITHOUT_ERROR = 0;
    /** Status of present errors and abort of the translation */
    static final int STATUS_EXIT_WITH_ERRORS = -1;

    /**
     * Main function called from the command line
     * @param args, command line arguments
     */
    public static void main(String[] args)
    {
        runMe(args);
    }

    /**
     * The main translator method
     * @return one of {@link trans#STATUS_OK}, {@link trans#STATUS_EXIT_WITH_ERRORS}, 
     * {@link trans#STATUS_EXIT_WITH_ERRORS}
     * indicating the status
     * 
     * Modified by LL on 16 Dec 2011.  Changed the return value to the
     * TLAtoPCalMapping object for the translation.  (The status return
     * value was not being used.)  If the translation fails, it returns
     * null.
     */
    /**
     * @param args
     * @return
     */
    /**
     * @param args
     * @return
     */
//    public static int runMe(String[] args)  
    public static TLAtoPCalMapping runMe(String[] args)   // added for testing
    {
        /*********************************************************************
        * Get and print version number.                                      *
        *********************************************************************/
        // String lastModified =
        // "last modified on Wed 11 March 2009 at 14:52:58 PST by lamport";
        /*******************************************************************
        * This string is inserted by an Emacs macro when a new version is  *
        * saved.  Unfortunately, Eclipse isn't Emacs, so the modification  *
        * date must be entered manually in the PcalParams module.          *
        *******************************************************************/

        if (ToolIO.getMode() == ToolIO.SYSTEM)
        {
            PcalDebug.reportInfo("pcal.trans Version " + PcalParams.version + " of " + PcalParams.modDate);
        }

        // SZ Mar 9, 2009:
        /*
         * This method is called in order to make sure, that  the
         * parameters are not sticky because these are could have been initialized
         * by the previous run  
         */
        PcalParams.resetParams();
        /*********************************************************************
        * Get and process arguments.                                         
        *********************************************************************/
        
        /**
         * Create the new TLAtoPCalMapping object, call it mapping
         * here and set PcalParams.tlaPcalMapping to point to it.
         */
        TLAtoPCalMapping mapping = new TLAtoPCalMapping() ;
        PcalParams.tlaPcalMapping = mapping;
        
        int status = parseAndProcessArguments(args);

        if (status != STATUS_OK)
        {
//            return exitWithStatus(status);
            return new TLAtoPCalMapping() ; // added for testing
        }

        /*********************************************************************
        * Read the input file, and set the Vector inputVec equal to its      *
        * contents, where inputVec[i] is the string containing the contents  *
        * of line i+1 of the input file.                                     *
        *********************************************************************/
        Vector inputVec = null;
        try
        {
            inputVec = fileToStringVector(PcalParams.TLAInputFile + /* (PcalParams.fromPcalFile ? ".pcal" : */".tla" /*)*/);
        } catch (FileToStringVectorException e)
        {
            PcalDebug.reportError(e);
//            return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
            return null ; // added for testing
        }

        /*********************************************************************
        * outputVec is an alias for inputVec if the input is a .tla file,    *
        * which was not always the case in the aborted version 1.31.         *
        *********************************************************************/
        // Vector outputVec = PcalParams.fromPcalFile ? new Vector() : inputVec;
        Vector outputVec = inputVec;

        /*********************************************************************
        * Set untabInputVec to be the vector of strings obtained from        *
        * inputVec by replacing tabs with spaces.                            *
        *                                                                    *
        * Tabs are date from the days when memory cost $1 per bit and are a  *
        * stupid anachronism.  They should be banned.  Although the various  *
        * methods taken from TLATeX should deal with tabs, there are         *
        * undoubtedly corner cases that don't work right.  In particular, I  *
        * think there's one case where PcalCharReader.backspace() might be   *
        * called to backspace over a tab.  It's easier to simply get rid of  *
        * the tabs than to try to make it work.                              *
        *                                                                    *
        * Since the user might be evil enough to prefer tabs, with tla-file  *
        * input, the parts of the output file that are not produced by the   *
        * translator are copied from inputVec, so any tabs the user wants    *
        * are kept.                                                          *
        *********************************************************************/
        Vector untabInputVec = removeTabs(inputVec);

        /**
         *  Look through the file for PlusCal options.  They are put anywhere
         *  in the file (either before or after the module or in a comment)
         *  with the following sequence
         *     PlusCal <optional white space> options <optional white space>
         *        ( <options> )
         *  
         *  where <options> has the same format as options on the command
         *  line.
         */
        IntPair searchLoc = new IntPair(0, 0);
        boolean notDone = true;
        while (notDone)
        {
            try
            {
                ParseAlgorithm.FindToken("PlusCal", untabInputVec, searchLoc, "");
                String line = ParseAlgorithm.GotoNextNonSpace(untabInputVec, searchLoc);
                String restOfLine = line.substring(searchLoc.two);
                if (restOfLine.startsWith("options"))
                {
                    // The first string after "PlusCal" not starting with a
                    // space character is "options"
                    if (ParseAlgorithm.NextNonIdChar(restOfLine, 0) == 7)
                    {
                        // The "options" should begin an options line
                        PcalParams.optionsInFile = true;
                        ParseAlgorithm.ProcessOptions(untabInputVec, searchLoc);
                        notDone = false;
                    }
                }
            } catch (ParseAlgorithmException e)
            {
                // The token "PlusCal" not found.
                notDone = false;
            }
        }

        /**
         * translationLine is set to the line of the output file at which
         * the \* BEGIN TRANSLATION appears--whether it is inserted into the
         * tla-file input by the user, or inserted into the output by the
         * translator for pcal-file input.
         */
        int translationLine = 0;

        /*********************************************************************
         * Set algLine, algCol to the line and column just after the string   *
         * [--]algorithm that begins the algorithm.  (These are Java          *
         * ordinals, in which counting begins at 0.)                          *
         *                                                                    *
         * Modified by LL on 18 Feb 2006 to use untabInputVec instead of      *
         * inputVec, to correct bug that occurred when tabs preceded the      *
         * "--algorithm".                                                     *
         *                                                                    *
         * For the code to handle pcal-input, I introduced the use of         *
         * IntPair objects to hold <line, column> Java coordinates (counting  *
         * from zero) in a file (or an image of a file in a String Vector).   *
         * For methods that advance through the file, the IntPair object is   *
         * passed as an argument and is advanced by the method.  This is      *
         * what I should have been doing from the start, but I wasn't smart   *
         * enough The IntPair curLoc is the main one used in the part of the  *
         * following code that handles pcal-file input.                       *
         *********************************************************************/
        int algLine = 0;
        int algCol = -1;
        /*******************************************************************
        * If the BEGIN/END TRANSLATION region exists, then set             *
        * translationLine to the number of the line after which the        *
        * translation is to be inserted and delete the previous version    *
        * of the translation (if it exists) from inputVec.  (Line          *
        * numbering is by Java ordinals.)  If the region doesn't exist,    *
        * set translationLine to -1.                                       *
        *                                                                  *
        * Note: we remove the previous version from inputVec, because      *
        * that's where the translated output is going to go, and also      *
        * from untabInputVec, because we will then detect if the begin     *
        * and end translation lines contain part of the algorithm within   *
        * them.                                                            *
        *******************************************************************/
        translationLine = findTokenPair(untabInputVec, 0, PcalParams.BeginXlation1, PcalParams.BeginXlation2);
        if (translationLine != -1)
        {
            

            int endTranslationLine = findTokenPair(untabInputVec, translationLine + 1, PcalParams.EndXlation1,
                PcalParams.EndXlation2);
            if (endTranslationLine == -1)
            {
                PcalDebug.reportError("No line containing `" + PcalParams.EndXlation1 + " " + PcalParams.EndXlation2);
//                return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
                return null;
            }

            endTranslationLine = endTranslationLine - 1;
            while (translationLine < endTranslationLine)
            {
                inputVec.remove(endTranslationLine);
                untabInputVec.remove(endTranslationLine);
                endTranslationLine = endTranslationLine - 1;
            }
        }

        // Search for "--algorithm" or "--fair".
        // If found set algLine and algCol right after the last char,
        // set foundBegin true, and set foundFairBegin true iff it
        // was "--fair".  Otherwise, set foundBegin false.
        boolean foundBegin = false;
        boolean foundFairBegin = false;
        while ((algLine < untabInputVec.size()) && !foundBegin)
        {
            String line = (String) untabInputVec.elementAt(algLine);
            algCol = line.indexOf(PcalParams.BeginAlg);
            if (algCol != -1)
            {
                algCol = algCol + PcalParams.BeginAlg.length();
                foundBegin = true;
            } else
            {
            	algCol = line.indexOf(PcalParams.BeginFairAlg);
            	if (algCol != -1) {
            		// Found the "--fair".  The more structurally nice thing to
            		// do here would be to move past the following "algorithm".
            		// However, it's easier to pass a parameter to the ParseAlgorithm
            		// class's GetAlgorithm method that tells it to go past the
            		// "algorithm" token.
            		 algCol = algCol + PcalParams.BeginFairAlg.length();
                     foundBegin = true;
                     foundFairBegin = true;
            		
            	} else {
            		algLine = algLine + 1;
            	} 
            }
            ;
        }
        ;
        if (!foundBegin)
        {
            PcalDebug.reportError("Beginning of algorithm string " + PcalParams.BeginAlg + " not found.");
//            return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
            return null ; // added for testing
        }
        ;
        
        /*
         * Set the algColumn and algLine fields of the mapping object.
         */
        mapping.algColumn = algCol;
        mapping.algLine = algLine;
        
        if (translationLine == -1) 
        {
           /****************************************************************
           * Insert BEGIN/END TRANSLATION comments immediately after the   *
           * end of the comment that contains the beginning of the         *
           * algorithm.  Set translationLine to the (Java) line number of  *
           * the BEGIN TRANSLATION.                                        *
           ****************************************************************/
        	
            // Set ecLine, ecCol to the position immediately after the
            // *) that closes the current comment.
        	int depth = 1 ;
            int ecLine = algLine ;
            int ecCol  = algCol ;
            boolean notFound = true ;
            while (notFound && ecLine < untabInputVec.size()) {
            	char[] line = ((String) untabInputVec.elementAt(ecLine)).toCharArray();
            	
                // check current line 
                while (notFound && ecCol < line.length-1)	 {
                	char ch = line[ecCol] ;
                	char ch2 = line[ecCol+1] ;
                	
// The following code isn't needed because the algorithm is inside a comment, and 
// quotes and \* have no effect in determining where the comment ends.
//
//                	if (ch == '"') {
//                		// gobble string
//                		ch = ch2 ;
//                		ecCol++ ;
//                		while (ch != '"') {
//                			if (ch == '\\') {
//                				ecCol = ecCol + 2;
//                			} 
//                			else {
//                				ecCol++ ;
//                			} ;
//                			if (ecCol < line.length - 1) {
//                			   ch = line[ecCol] ;
//                			}
//                			else {
//                				ch = '"' ;
//                			}
//                		} ;
//                		ecCol++ ;
//                	} 
//                        	
//                	if (ch == '\\' && ch2 == '*' ) {
//                		// end of line comment, skip to end of line
//                		ecCol = 214748364;  // a very large int
//                	}
                	if (ch == '(' && ch2 == '*') {
                		// left comment delimiter
                    	depth++;
                    	ecCol = ecCol + 2;
                	}
                	else if (ch == '*' && ch2 == ')') {
                		// right comment delimiter
                		depth--;
                		ecCol = ecCol + 2;
                		if (depth == 0) {
                			notFound = false ;
                		}
                	}
                	else {
                		// not an interesting character
                		ecCol++ ;
                	}
                }
            	
            	// if not found, go to next line
            	if (notFound) {
            		ecLine++ ;
            		ecCol = 0;
            	}
            }
            
            if (notFound) {
            	PcalDebug.reportError("Algorithm not in properly terminated comment");
//                return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
                return null ; // added for testing
            }
            
            // Report an error  if there's something else on the line that doesn't begin with "\*".  This is probably
            
            String endStuff = ((String) untabInputVec.elementAt(ecLine)).substring(ecCol).trim() ;
            
            if (!endStuff.equals("") && !endStuff.startsWith("\\*")) {
            	PcalDebug.reportError("Text on same line following `*)' that ends the \n   comment containing the algorithm.");
//                return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
                return null ; // added for testing
            } ;
            
            inputVec.insertElementAt("\\* BEGIN TRANSLATION", ecLine+1) ;
            untabInputVec.insertElementAt("\\* BEGIN TRANSLATION", ecLine+1) ;
            inputVec.insertElementAt("\\* END TRANSLATION", ecLine+2) ;
            untabInputVec.insertElementAt("\\* END TRANSLATION", ecLine+2) ;

            translationLine = ecLine + 1;
//System.out.println(ecLine + ", " + ecCol);
//Debug.printVector(inputVec, "foo");
        }
        
        /*
         * Set the mappings start line.
         */
        mapping.tlaStartLine = translationLine + 1; 

        /*********************************************************************
        * Added by LL on 18 Feb 2006 to fix bugs related to handling of      *
        * comments.                                                          *
        *                                                                    *
        * Remove all comments from the algorithm in untabInputVec,           *
        * replacing (* *) comments by spaces to keep the algorithm tokens    *
        * in the same positions for error reporting.                         *
        *********************************************************************/
        try
        {
            ParseAlgorithm.uncomment(untabInputVec, algLine, algCol);
        } catch (ParseAlgorithmException e)
        {
            PcalDebug.reportError(e);
//            return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
            return null ; // added for testing
        }
        // } // end else of if (PcalParams.fromPcalFile) -- i.e., end processing
        // of .tla input file.

        /*********************************************************************
        * Set reader to a PcalCharReader for the input file (with tabs and   *
        * the previous translation removed), starting right after the        *
        * PcalParams.BeginAlg string.                                        *
        *********************************************************************/
        PcalCharReader reader = new PcalCharReader(untabInputVec, algLine, algCol, inputVec.size(), 0);

        /*********************************************************************
        * Set ast to the AST node representing the entire algorithm.         *
        *********************************************************************/
        AST ast = null;
        try
        {
            ast = ParseAlgorithm.getAlgorithm(reader, foundFairBegin);
// System.out.println(ast.toString());
// For testing, we print out when the new code for eliminating the 
// suttering-on-done and pc is used.
// if (ParseAlgorithm.omitPC || ParseAlgorithm.omitStutteringWhenDone) {
//  System.out.println("omit pc = " + ParseAlgorithm.omitPC + 
//          ", omitStutteringWhenDone = " + ParseAlgorithm.omitStutteringWhenDone);
// }

        } catch (ParseAlgorithmException e)
        {
            PcalDebug.reportError(e);
//            return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
            return null ; // added for testing
        }
        PcalDebug.reportInfo("Parsing completed.");
// tla-pcal debugging
//System.out.println("Translation Output:");
//System.out.println(ast.toString());
        /*********************************************************************
        * For -writeAST option, just write the file AST.tla and halt.        *
        *********************************************************************/
        if (PcalParams.WriteASTFlag)
        {
            WriteAST(ast);
//            return exitWithStatus(STATUS_EXIT_WITHOUT_ERROR);
            return null ; // added for testing
        }
        ;

        /*********************************************************************
        * Rename algorithm variables to eliminate name conflicts--for        *
        * example, if the same variable is declared inside different         *
        * procedures, if a variable name and a label are the same, or if     *
        * the same label is used in to different procedures.  This should    *
        * also report an error and terminate if it discovers a conflict      *
        * between the variable of a `with' statement and some other          *
        * identifier in the algorithm.  It should also detect other          *
        * conflicts--for example, if there is a variable named "Init" or     *
        * "TRUE".  However, there are conflicts that the translator can't    *
        * spot--for example, if a variable name is the same as the name of   *
        * some operator defined elsewhere in the TLA+ module.  So it's not   *
        * worth going overboard in this checking.                            *
        *********************************************************************/

        // SZ February.15 2009: made non-static to make PCal stateless for tool runs
        PCalTLAGenerator pcalTLAGenerator = new PCalTLAGenerator(ast);
        try
        {
            pcalTLAGenerator.removeNameConflicts();
        } catch (RemoveNameConflictsException e1)
        {
            PcalDebug.reportError(e1);
//            return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
            return null ; // added for testing
        }

        /*********************************************************************
        * Set the vector `translation' to the translation of the algorithm   *
        * represented by the AST ast.  If called with the -spec option,      *
        * do the translation by calling TLC. Otherwise, call the ordinary    *
        * Translate method.                                                  *
        *********************************************************************/
        Vector translation = null;
        boolean tlcTranslation = PcalParams.SpecOption || PcalParams.MyspecOption || PcalParams.Spec2Option
                || PcalParams.Myspec2Option;

        if (tlcTranslation)
        {
            try
            {
                translation = TLCTranslate(ast);
            } catch (TLCTranslationException e)
            {
                PcalDebug.reportError(e);
//                return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
                return null ; // added for testing
            }
        } else
        {
            try
            {
                translation = pcalTLAGenerator.translate();
            } catch (RemoveNameConflictsException e)
            {
                PcalDebug.reportError(e);
//                return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
                return null ; // added for testing
            }
        }
        ;

        PcalDebug.reportInfo("Translation completed.");
// tla-pcal Debugging
//System.exit(0);
        /*********************************************************************
        * For .tla input:                                                    *
        * Rename the old file by changing its extension from "tla" to "old". *
        *********************************************************************/
        // if (!PcalParams.fromPcalFile)
        // {
        File file;
        try
        {
            file = new File(PcalParams.TLAInputFile + ".old");
            if (file.exists())
            {
                file.delete();
            }
            ;
            file = new File(PcalParams.TLAInputFile + ".tla");
            file.renameTo(new File(PcalParams.TLAInputFile + ".old"));
        } catch (Exception e)
        {
            PcalDebug.reportError("Could not rename input file " + PcalParams.TLAInputFile + ".tla" + " to "
                    + PcalParams.TLAInputFile + ".old");
//            return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
            return null ; // added for testing
        }
        ;
        // }

        /*********************************************************************
        * Add the translation to outputVec.                                  *
        *********************************************************************/
        int i = 0;
        while (i < translation.size())
        {
            outputVec.insertElementAt(translation.elementAt(i), i + translationLine + 1);
            i = i + 1;
        }

        /*********************************************************************
        * Code from aborted version 1.31.                                    *
        * For .pcal input, set outputSuffixLoc and add the rest of the       *
        * input file to the output.                                          *
        *********************************************************************/
        // if (PcalParams.fromPcalFile)
        // {
        // PcalParams.outputSuffixLoc = new IntPair(outputVec.size(), 0);
        // // if there's stuff in the suffix on the same line with the
        // // end of the algorithm, write it on a separate line.
        // IntPair curLoc = new IntPair(PcalParams.inputSuffixLoc.one, PcalParams.inputSuffixLoc.two);
        // if (curLoc.one < untabInputVec.size())
        // {
        // String lastLine = (String) untabInputVec.elementAt(curLoc.one);
        // if (curLoc.two < lastLine.length())
        // {
        // outputVec.addElement(lastLine.substring(curLoc.two));
        // }
        // curLoc.one++;
        // }
        // // Copy the rest of the input file into the output file.
        // for (int ii = curLoc.one; ii < untabInputVec.size(); ii++)
        // {
        // outputVec.addElement((String) untabInputVec.elementAt(ii));
        // }
        // }
        /*********************************************************************
        * Write the output file.                                             *
        *********************************************************************/
        try
        {
            WriteStringVectorToFile(outputVec, PcalParams.TLAInputFile + ".tla");
        } catch (StringVectorToFileException e)
        {
            PcalDebug.reportError(e);
//            return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
            return null ; // added for testing
        }

        PcalDebug.reportInfo("New file " + PcalParams.TLAInputFile + ".tla" + " written.");

        /*********************************************************************
        * Write the cfg file, unless the -nocfg option is used.              *
        *********************************************************************/
        File cfgFile = new File(PcalParams.TLAInputFile + ".cfg");
        Vector cfg = null;
        boolean writeCfg = !PcalParams.Nocfg;
        if (writeCfg && cfgFile.exists())
        {
            if (cfgFile.canRead())
            {
                try
                {
                    cfg = fileToStringVector(PcalParams.TLAInputFile + ".cfg");
                } catch (FileToStringVectorException e)
                {
                    PcalDebug.reportError(e);
//                    return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
                    return null ; // added for testing
                }
            } else
            {
                /*************************************************************
                * cfg file is read-only.                                     *
                *************************************************************/
                writeCfg = false;
                PcalDebug.reportInfo("File " + PcalParams.TLAInputFile + ".cfg is read only, new version not written.");
            }
        } else
        {
            cfg = new Vector();
            cfg.addElement(PcalParams.CfgFileDelimiter);
        }
        ;

        /*********************************************************************
        * Delete previously written part of cfg file.                        *
        *********************************************************************/
        if (writeCfg)
        {
            i = 0;
            boolean done = false;
            while ((!done) && (cfg.size() > i))
            {
                if (((String) cfg.elementAt(i)).indexOf(PcalParams.CfgFileDelimiter) == -1)
                {
                    i = i + 1;
                } else
                {
                    done = true;
                }
            }
            if (done)
            {
                /*************************************************************
                * Delete all lines before the delimiting comment string.     *
                *************************************************************/
                while (i > 0)
                {
                    cfg.removeElementAt(0);
                    i = i - 1;
                }
            } else
            {
                /*************************************************************
                * The delimiting comment string written by the translator    *
                * not found in the cfg file, so presumably the user created  *
                * the cfg file before running the translator on the input    *
                * file.  We insert the delimiter.                            *
                *************************************************************/
                cfg.add(0, PcalParams.CfgFileDelimiter);
            }
            ;

            /******************************************************************
            * If defaultInitValue is used, add a CONSTANT statement setting   *
            * it to a model value of the same name.                           *
            * (Added 22 Aug 2007 by LL.)                                      *
            ******************************************************************/
            if (tlcTranslation || ParseAlgorithm.hasDefaultInitialization)
            {
                cfg.add(0, "CONSTANT defaultInitValue = defaultInitValue");
            }
            ;
            /******************************************************************
            * Insert the `PROPERTY Termination' line if requested.            *
            ******************************************************************/
            if (PcalParams.CheckTermination)
            {
                cfg.add(0, "PROPERTY Termination");
            }
            ;

            /******************************************************************
            * Insert the SPECIFICATION line if there isn't already one.       *
            ******************************************************************/
            i = 0;
            boolean hasSpec = false;
            while (i < cfg.size())
            {
                String thisLine = (String) cfg.elementAt(i);
                if ((thisLine.indexOf("SPECIFICATION") != -1)
                        && ((thisLine.indexOf("\\*") == -1) || (thisLine.indexOf("\\*") > thisLine
                                .indexOf("SPECIFICATION"))))
                {
                    hasSpec = true;
                }
                ;
                i = i + 1;
            }
            ;
            if (hasSpec)
            {
                PcalDebug.reportInfo("File " + PcalParams.TLAInputFile
                        + ".cfg already contains SPECIFICATION statement," + "\n   so new one not written.");
            } else
            {
                cfg.add(0, "SPECIFICATION Spec");
            }
            ;
            try
            {
                WriteStringVectorToFile(cfg, PcalParams.TLAInputFile + ".cfg");
            } catch (StringVectorToFileException e)
            {
                PcalDebug.reportError(e);
//                return exitWithStatus(STATUS_EXIT_WITH_ERRORS);
                return null ; // added for testing
            }
            PcalDebug.reportInfo("New file " + PcalParams.TLAInputFile + ".cfg" + " written.");
        }
        ;

//        return exitWithStatus(STATUS_EXIT_WITHOUT_ERROR);
        return PcalParams.tlaPcalMapping ; // added for testing
    } // END main

    /**
     * If run in the system mode, exits the program, in tool mode returns the status
     * @param status
     */
    private static int exitWithStatus(int status)
    {
        if (ToolIO.getMode() == ToolIO.SYSTEM)
        {
            // return exit status in system mode
            System.exit(status);
        }

        // just exit the function in tool mode
        return status;
    }

    /********************** Writing the AST ************************************/
    private static boolean WriteAST(AST ast)
    {
        Vector astFile = new Vector();
        astFile.addElement("------ MODULE AST -------");
        astFile.addElement("EXTENDS TLC");
        astFile.addElement("fairness == \"" + PcalParams.FairnessOption + "\"");
        astFile.addElement(" ");
        astFile.addElement("ast == ");
        astFile.addElement(ast.toString());
        astFile.addElement("==========================");
        try
        {
            WriteStringVectorToFile(astFile, "AST.tla");
        } catch (StringVectorToFileException e)
        {
            PcalDebug.reportError(e);
            return false;
        }
        PcalDebug.reportInfo("Wrote file AST.tla.");
        return true;
    }

    /************************* THE TLC TRANSLATION *****************************/

    private static Vector TLCTranslate(AST ast) throws TLCTranslationException
    /***********************************************************************
    * The result is a translation of the algorithm represented by ast      *
    * obtained by using TLC to execute the definition of Translation(ast)  *
    * in the TLA+ module PlusCal.  It equals a vector with a single        *
    * element, which is the entire translation as a single string.         *
    *                                                                      *
    * This method relies on a bug in TLC's pretty-print routine that       *
    * causes it not to work properly on the output produced by the TLA     *
    * spec.  Instead of prettyprinting the output as                       *
    *                                                                      *
    *   << "VARIABLES ...",                                                *
    *      "vars == ... ",                                                 *
    *      ...                                                             *
    *   >>                                                                 *
    *                                                                      *
    * it prints the entire translation on a single line as                 *
    *                                                                      *
    *   << "VARIABLES ...", "vars == ... ", ... >>                         *
    *                                                                      *
    * This allows the method to find the entire translation as the single  *
    * line that begins with "<<".  If this TLC bug is fixed, then the      *
    * TLCTranslate method will have to be modified to read the spec as a   *
    * sequence of lines.  This will probably require the TLA module that   *
    * translates the spec to print a special marker line to indicate the   *
    * end of the translation.                                              *
    ***********************************************************************/
    {
        /*********************************************************************
        * Write the file AST.tla that contains                               *
        *********************************************************************/
        WriteAST(ast);

        /*********************************************************************
        * For the -spec (rather than -myspec) option, copy the               *
        * specification's .tla and .cfg files PlusCal.tla to current         *
        * directory.                                                         *
        *********************************************************************/
        if (PcalParams.SpecOption || PcalParams.Spec2Option)
        {
            try
            {
                Vector parseFile = PcalResourceFileReader.ResourceFileToStringVector(PcalParams.SpecFile + ".tla");

                WriteStringVectorToFile(parseFile, PcalParams.SpecFile + ".tla");
                parseFile = PcalResourceFileReader.ResourceFileToStringVector(PcalParams.SpecFile + ".cfg");
                WriteStringVectorToFile(parseFile, PcalParams.SpecFile + ".cfg");

                PcalDebug
                        .reportInfo("Wrote files " + PcalParams.SpecFile + ".tla and " + PcalParams.SpecFile + ".cfg.");

            } catch (UnrecoverableException e)
            {
                throw new TLCTranslationException(e.getMessage());
            }

        }
        ;
        /*********************************************************************
        * Run TLC on the specification file and set tlcOut to TLC's output.  *
        *********************************************************************/
        String javaInvocation;
        if (PcalParams.SpecOption || PcalParams.MyspecOption)
        {
            // Modified on 29 May 2010 by LL so tlc2 is run in
            // all cases.
            PcalDebug.reportInfo("Running TLC2.");
            javaInvocation = "java -Xss1m tlc2.TLC ";
        } else
        {
            PcalDebug.reportInfo("Running TLC2.");
            javaInvocation = "java -Xss1m tlc2.TLC ";
        }
        ;
        String tlcOut = "      ";
        Runtime rt = Runtime.getRuntime();
        try
        {
            // Modified on 29 May 2010 by LL to replace getErrorStream() with 
            // getInputStream(), which by Java logic gets standard out.  (And no,
            // getErrorStream() did not get standard non-error.)  Apparently,
            // TLC has been changed to put its output on stdout.
            BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(rt.exec(
                    javaInvocation + PcalParams.SpecFile).getInputStream()));
            while (tlcOut.indexOf("<<") == -1)
            {
                tlcOut = bufferedReader.readLine();
            }
            ;
            bufferedReader.close();
        } catch (Exception e)
        {
            throw new TLCTranslationException("Error reading output of TLC");
        }
        ;

        /*********************************************************************
        * Test if the translation failed and reported an error message,      *
        * bracketed by "@Error@" and "@EndError@" strings.  If it did,       *
        * report the error and halt.  If not, set tlcOut to the value of     *
        * Translation(ast) with the outermost "<<" and ">>" removed.         *
        *********************************************************************/
        if (tlcOut.indexOf("@Error@") != -1)
        {
            throw new TLCTranslationException("TLC's translation of the parsed algorithm failed with\n  Error: "
                    + tlcOut.substring(tlcOut.indexOf("@Error@") + 7, tlcOut.indexOf("@EndError@")));
        }
        ;
        tlcOut = tlcOut.substring(2, tlcOut.lastIndexOf(">>")) + "  ";
        PcalDebug.reportInfo("Read TLC output.");

        /*********************************************************************
        * Set transl to the string obtained by converting tlcOut, which is   *
        * a comma-separated sequence of strings, to the single string that   *
        * they represent.  See PlusCal.tla for an explanation of the         *
        * encoding of TLA+ statements as sequences of strings.               *
        *********************************************************************/
        int i = 0;
        String transl = "";
        while (i < tlcOut.length())
        {
            if (tlcOut.charAt(i) == '"')
            {
                i = i + 1;
                if ((tlcOut.charAt(i) == '\\') && (tlcOut.charAt(i + 1) == '"'))
                /*******************************************************
                * This is a quoted string.                             *
                *******************************************************/
                {
                    if (tlcOut.charAt(i + 2) != '"')
                    {
                        throw new TLCTranslationException("I'm confused");

                    }
                    ;
                    i = i + 3;
                    while (tlcOut.charAt(i) != '"')
                    {
                        i = i + 1;
                    }
                    i = i + 1;
                    transl = transl + "\"";
                    while (tlcOut.charAt(i) != '"') // "
                    {
                        if (tlcOut.charAt(i) == '\\')
                        {
                            /***********************************************
                            * Get special character.                       *
                            ***********************************************/
                            transl = transl + tlcOut.substring(i, i + 2);
                            i = i + 2;
                        } else
                        {
                            transl = transl + tlcOut.substring(i, i + 1);
                            i = i + 1;
                        }
                        ;
                    }
                    ;
                    i = i + 8;
                    transl = transl + "\"";
                } else
                {
                    while (tlcOut.charAt(i) != '"')
                    {
                        if ((tlcOut.charAt(i) == '\\') && (tlcOut.charAt(i + 1) == '\\'))
                        {
                            i = i + 1;
                        }
                        ;
                        transl = transl + tlcOut.substring(i, i + 1);
                        i = i + 1;
                    }
                    ;
                    i = i + 1;
                }
                ;
            } // END if (tlcOut.charAt(i) == '"')
            else if (tlcOut.charAt(i) == ',')
            {
                i = i + 1;
            } else
            {
                if (tlcOut.charAt(i) != ' ')
                {
                    throw new TLCTranslationException("Expected space but found `" + tlcOut.charAt(i) + "'");
                }
                ;
                transl = transl + tlcOut.substring(i, i + 1);
                i = i + 1;
            }
            ;
        }
        ; // END while
        /* ******************************************************************
         * Wrap the translated string into approximately 80 character lines *
         *******************************************************************/
        transl = WrapString(transl, 78);
        Vector result = new Vector();
        result.addElement(transl);
        return result;
    }

    /***************** METHODS FOR READING AND WRITING FILES *****************/

    private static void WriteStringVectorToFile(Vector inputVec, String fileName) throws StringVectorToFileException
    /***********************************************************************
    * Writes the Vector of strings inputVec to file named fileName, with   *
    * each element of inputVec written on a new line.                      *
    ***********************************************************************/
    {
        try
        {
            // I have no idea what Java does if you try to write a new version
            // of a read-only file. On Windows, it's happy to write it. Who
            // the hell knows what it does on other operating systems? So, something
            // like the following code could be necessary. However, the setWritable()
            // method was introduced in Java 1.6, and in December 2009, that version
            // isn't available on the Mac. And I can't find out how to set a file
            // to be writable in any earlier version of Java. On the web, the advice
            // is to copy the file, delete the old version, and rename the copy.
            // But the File method's documentation actually says that delete may or
            // may not delete the read-only file, depending on the OS.
            //
            // File file = new File(fileName);
            // if (! file.canWrite()) {
            // file.setWritable(true);
            // }
            BufferedWriter fileW = new BufferedWriter(new FileWriter(fileName));
            int lineNum = 0;
            while (lineNum < inputVec.size())
            {
                fileW.write((String) inputVec.elementAt(lineNum));
                fileW.newLine();
                lineNum = lineNum + 1;
            }
            ;
            fileW.close();
        } catch (Exception e)
        {
            throw new StringVectorToFileException("Could not write file " + fileName);
        }
        ;

    }

    private static Vector fileToStringVector(String fileName) throws FileToStringVectorException
    /***********************************************************************
    * Reads file fileName into a StringVector, a vector in which each      *
    * element is a line of the file.                                       *
    ***********************************************************************/
    {
        Vector inputVec = new Vector(100);
        try
        {
            BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));
            try
            {
                String nextLine = bufferedReader.readLine();
                while (nextLine != null)
                {
                    inputVec.addElement(nextLine);
                    nextLine = bufferedReader.readLine();
                }
                ;
                bufferedReader.close();
            } catch (IOException e)
            {
                /*********************************************************
                * Error while reading input file.                        *
                *********************************************************/
                throw new FileToStringVectorException("Error reading file " + fileName + ".");
            }
        }

        catch (FileNotFoundException e)
        {
            /**************************************************************
            * Input file could not be found.                              *
            **************************************************************/
            throw new FileToStringVectorException("Input file " + fileName + " not found.");
        }
        ;
        return inputVec;
    }

    /********************* PROCESSING THE COMMAND LINE ***********************/

    /**
     * Processes the command line arguments
     * 
     * This method changes values of public static variables of the {@link PcalParams} 
     * 
     * SZ: This will cause problems, due to the fact that the PCalParams are static.
     * Any initialization should overwrite the previous, which is currently NOT the case
     * Should be re-factored to non-static access to the properties
     * 
     * @return status of processing. 
     *  the status {@link trans#STATUS_OK} indicates that no errors has been detected.
     *  the status {@link trans#STATUS_EXIT_WITHOUT_ERROR} indicates that no errors has been found but translation
     *   should not be started (e.G -help call)
     *  the status {@link trans#STATUS_EXIT_WITH_ERRORS} indicates errors 
     *  
     * Change made on 9 December 2009 for pcal-file input.  This procedure is
     * called a second time if there is pcal-file input with an options statement.
     * It will be the second call iff {@link PcalParams#optionsInFile} equals true.
     * The second call should have a dummy extra argument in place of the 
     * command-line's file-name argument.   When pcal files were eliminated, this
     * kludgy mechanism was kept and used to indicate if the method is being called
     * for options specified inside the module. 
     */
    static int parseAndProcessArguments(String[] args)
    {

        /** *******************************************************************
         *<pre>
         * Get the command-line arguments and set the appropriate parameters.  *
         * The following command line arguments are handled.  Only the ones    *
         * marked with ** besides them can be specified in the module file's   *
         * options statement.  The "-" can be omitted when the option is in    *
         * the module file's options statement.                                *
         *                                                                     *
         *   -help  : Type a help file instead of running the program.         *
         *                                                                     *
         *** -spec name : Uses TLC and the TLA+ specification name.tla to do   *
         *                the translation.  The files name.tla and name.cfg    *
         *                are copied from the java/ directory to the current   *
         *                directory; the file AST.tla that defines `fairness'  *
         *                to equal the fairness option and `ast' to equal      *
         *                the the AST data structure representing the          *
         *                algorithm is written to the current directory; and   *
         *                TLC is run on name.tla to produce the translation.   *
         *                                                                     *
         *** -myspec name : Like -spec, except it finds the files names.tla    *
         *                  and names.cfg in the current directory, instead    *
         *                  of writing them there.                             *
         *                                                                     *
         *   -spec2   name                                                     *
         *   -myspec2 name : Like -spec and -myspec, except they use TLC2      *
         *                   instead of TLC (aka TLC1).                        *
         *                                                                     *
         *   -writeAST : Writes the AST file as in the -spec option, but does  *
         *               not perform the translation.                          *
         *                                                                     *
         *   -debug : Run in debugging mode, whatever that means.  For the     *
         *            parser, it just means that the toString() methods        *
         *            output the line and column number along with the         *
         *            node.                                                    *
         *                                                                     *
         *   -unixEOL : Forces the use of Unix end-of-line convention,         *
         *              regardless of the system's default.  Without this,     *
         *              when run on Windows, the files it writes seem to have  *
         *              a "^M" at the end of every line when viewed with       *
         *              Emacs.                                                 *
         *                                                                     *
         *** -wf : Conjoin to formula Spec weak fairness of each process's     *
         *         next-state action                                           *
         *                                                                     *
         *** -sf : Conjoin to formula Spec strong fairness of each process's   *
         *         next-state action                                           *
         *                                                                     *
         *** -wfNext : Conjoin to formula Spec weak fairness of the entire     *
         *             next-state action                                       *
         *                                                                     *
         *** -nof : Conjoin no fairness formula to Spec.  This is the default, *
         *          except when the -termination option is chosen.             *
         *                                                                     *
         *** -termination : Add to the .cfg file the command                   *
         *                     PROPERTY Termination                            *
         *                                                                     *
         *   -nocfg : Suppress writing of the .cfg file.                       *
         *                                                                     *
         *                                                                     *
         *** -noDoneDisjunct : Suppress the disjunct of the next-state         *
         *                     relation that describes stuttering steps taken  *
         *                     when the algorithm has halted.                  *
         *                                                                     *
         *** -label : Tells the translator to add missing labels.  This is     *
         *            the default only for a uniprocess algorithm in which     *
         *            the user has typed no labels.                            *
         *                                                                     *
         *   -reportLabels : True if the translator should print the names     *
         *                   and locations of all labels it adds.  Like        *
         *                   -label, it tells the translator to add missing    *
         *                   labels.                                           *
         *                                                                     *
         *** -labelRoot name : If the translator adds missing labels, it       *
         *                     names them name1, name2, etc.  Default value    *
         *                     is "Lbl_".                                      *
         *                                                                     *
         *  THE FOLLOWING OPTIONS ADDED IN VERSION 1.4                         *
         *                                                                     *
         *** -lineWidth : The translation tries to perform the translation so  *
         *                lines have this maximum width.  (It will often       *
         *                fail.)  Default is 78, minimum value is 60.          *
         *                                                                     *
         *** -version : The version of PlusCal for which this algorithm is     *
         *              written.  If the language is ever changed to make      *
         *              algorithms written for earlier versions no longer      *
         *              legal, then the translator should do the appropriate   *
         *              thing when the earlier version number is specified.    *                
         *</pre>
         ********************************************************************* */
        boolean inFile = PcalParams.optionsInFile;
        boolean notInFile = !inFile;
        // Just convenient abbreviations
        boolean firstFairness = inFile;
        // Used to allow a fairness property specified by a command-line
        // option to be overridden by one in the pcal-file's options statement.
        // It is set false when the first fairness property is set from
        // the options statement.
        boolean explicitNof = false;
        // Set true when the "nof" fairness option is set by an explicit
        // user request, rather than by default. It was added to fix
        // a bug in -termination introduced in version 1.4 by having
        // the options statement in the file. I think option processing
        // can be simplified to eliminate this, but it's easier to add
        // this kludge.
        int nextArg = 0;
        /******************************************************************
        * The number of the argument being processed.                     *
        ******************************************************************/
        int maxArg = args.length - 1;
        /******************************************************************
        * The number of option arguments.  (For processing command-line   *
        * arguments, the last element of args is the input-file name.)    *
        ******************************************************************/
        if (maxArg < 0)
        {
            return CommandLineError("No arguments specified");
        }

        if (notInFile && (args[maxArg].length() != 0) && (args[maxArg].charAt(0) == '-'))
        /******************************************************************
        * If the last argument begins with "-", then no file has been     *
        * specified.  This should mean that the user has typed "-help",   *
        * but it could be a mistake.  But let's just assume she typed     *
        * "-help", since she either wants or needs help.                  *
        ******************************************************************/
        {
            if (OutputHelpMessage())
            {
                return STATUS_EXIT_WITHOUT_ERROR;

            } else
            {
                return STATUS_EXIT_WITH_ERRORS;
            }
        }

        while (nextArg < maxArg)
        /*******************************************************************
        * Process all the arguments, except for the input-file name.       *
        *******************************************************************/
        {
            String option = args[nextArg];
            if (notInFile && option.equals("-help"))
            {
                if (OutputHelpMessage())
                {
                    return STATUS_EXIT_WITHOUT_ERROR;
                } else
                {
                    return STATUS_EXIT_WITH_ERRORS;
                }
            } else if (notInFile && option.equals("-writeAST"))
            {
                PcalParams.WriteASTFlag = true;
                if (CheckForConflictingSpecOptions())
                {
                    return STATUS_EXIT_WITH_ERRORS;
                }
            } else if (option.equals("-spec") || 
                        (inFile && option.equals("spec")))
            {
                PcalParams.SpecOption = true;
                if (CheckForConflictingSpecOptions())
                {
                    return STATUS_EXIT_WITH_ERRORS;
                }
                nextArg = nextArg + 1;
                if (nextArg == maxArg)
                {
                    return CommandLineError("Specification name must follow `-spec' option");
                }
                PcalParams.SpecFile = args[nextArg];
            } else if (option.equals("-myspec") || 
                    (inFile && option.equals("myspec")))
            {
                PcalParams.MyspecOption = true;
                if (CheckForConflictingSpecOptions())
                {
                    return STATUS_EXIT_WITH_ERRORS;
                }
                nextArg = nextArg + 1;
                if (nextArg == maxArg)
                {
                    return CommandLineError("Specification name must follow `-myspec' option");
                }
                PcalParams.SpecFile = args[nextArg];
            } else if (notInFile && option.equals("-spec2"))
            {
                PcalParams.Spec2Option = true;
                if (CheckForConflictingSpecOptions())
                {
                    return STATUS_EXIT_WITH_ERRORS;
                }
                ;
                nextArg = nextArg + 1;
                if (nextArg == maxArg)
                {
                    return CommandLineError("Specification name must follow `-spec' option");
                }
                PcalParams.SpecFile = args[nextArg];
            } else if (notInFile && option.equals("-myspec2"))
            {
                PcalParams.Myspec2Option = true;
                if (CheckForConflictingSpecOptions())
                {
                    return STATUS_EXIT_WITH_ERRORS;
                }
                ;
                nextArg = nextArg + 1;
                if (nextArg == maxArg)
                {
                    return CommandLineError("Specification name must follow `-myspec' option");
                }
                PcalParams.SpecFile = args[nextArg];
            } else if (notInFile && option.equals("-debug"))
            {
                PcalParams.Debug = true;
            } else if (notInFile && option.equals("-unixEOL"))
            {
                System.setProperty("line.separator", "\n");
            } else if (option.equals("-termination") || (inFile && option.equals("termination")))
            {
                PcalParams.CheckTermination = true;
            } else if (option.equals("-nocfg"))
            {
                PcalParams.Nocfg = true;
            } else if (option.equals("-noDoneDisjunct") || (inFile && option.equals("noDoneDisjunct")))
            {
                PcalParams.NoDoneDisjunct = true;
            } else if (option.equals("-wf") || (inFile && option.equals("wf")))
            {
                if (firstFairness)
                {
                    PcalParams.FairnessOption = "";
                    firstFairness = false;
                }
                if (!PcalParams.FairnessOption.equals(""))
                {
                    return CommandLineError("Can only have one of -wf, -sf, -wfNext, " + "and -nof options");
                }
                PcalParams.FairnessOption = "wf";
            } else if (option.equals("-sf") || (inFile && option.equals("sf")))
            {
                if (firstFairness)
                {
                    PcalParams.FairnessOption = "";
                    firstFairness = false;
                }
                if (!PcalParams.FairnessOption.equals(""))
                {
                    return CommandLineError("Can only have one of -wf, -sf, -wfNext, " + "and -nof options");
                }
                PcalParams.FairnessOption = "sf";
            } else if (option.equals("-wfNext") || (inFile && option.equals("wfNext")))
            {
                if (firstFairness)
                {
                    PcalParams.FairnessOption = "";
                    firstFairness = false;
                }
                if (!PcalParams.FairnessOption.equals(""))
                {
                    return CommandLineError("Can only have one of -wf, -sf, -wfNext, " + "and -nof options");
                }
                PcalParams.FairnessOption = "wfNext";
            } else if (option.equals("-nof") || (inFile && option.equals("nof")))
            {
                if (firstFairness)
                {
                    PcalParams.FairnessOption = "";
                    firstFairness = false;
                }
                if (!PcalParams.FairnessOption.equals(""))
                {
                    return CommandLineError("Can only have one of -wf, -sf, -wfNext, " + "and -nof options");
                }
                PcalParams.FairnessOption = "nof";
                explicitNof = true;
            } else if (option.equals("-label") || (inFile && option.equals("label")))
            {
                PcalParams.LabelFlag = true;
            } else if (notInFile && option.equals("-reportLabels"))
            {
                PcalParams.ReportLabelsFlag = true;
                PcalParams.LabelFlag = true;
            } else if (option.equals("-labelRoot") || (inFile && option.equals("labelRoot")))
            {
                nextArg = nextArg + 1;
                if (nextArg == maxArg)
                {
                    return CommandLineError("Label root must follow `-labelRoot' option");
                }
                PcalParams.LabelRoot = args[nextArg];
            }
            // else if (option.equals("-readOnly") || (pcal && option.equals("readOnly"))) {
            // PcalParams.readOnly = true;
            // }
            // else if (option.equals("-writable") || (pcal && option.equals("writable"))) {
            // PcalParams.readOnly = false;
            // }
            else if (option.equals("-version") || (inFile && option.equals("version")))
            {
                nextArg = nextArg + 1;
                if (nextArg == maxArg)
                {
                    return CommandLineError("Version number must follow `-version' option");
                }
                if (!PcalParams.ProcessVersion(args[nextArg]))
                {
                    return CommandLineError("Bad version number");
                }

            } else if (option.equals("-lineWidth"))
            {
                nextArg = nextArg + 1;
                try
                {
                    if (nextArg == maxArg)
                    {
                        throw new NumberFormatException();
                    }
                    int a = new Integer(args[nextArg]).intValue();
                    if (a < 60)
                    {
                        throw new NumberFormatException();
                    }
                    PcalTLAGen.wrapColumn = a;
                    PcalTLAGen.ssWrapColumn = a - 33;
                } catch (Exception e)
                {
                    return CommandLineError("Integer value at least 60 must follow `-lineWidth' option");
                }

            } else
            {
                if (notInFile)
                {
                    return CommandLineError("Unknown command-line option: " + option);
                } else
                {
                    return CommandLineError("Unknown or illegal option in options statement: " + option);
                }
            }
            ;
            nextArg = nextArg + 1;
        } // END while (nextArg < maxArg)

        if (nextArg > maxArg)
        /******************************************************************
        * The last option took an argument that was the last              *
        * command-line argument.                                          *
        ******************************************************************/
        {
            return CommandLineError("No input file specified");
        }

        // SZ 02.16.2009: since this is a modification of the parameters, moved
        // to the parameter handling method
        if (PcalParams.FairnessOption.equals("-nof"))
        {
            PcalParams.FairnessOption = "";
        }
        if (PcalParams.CheckTermination && PcalParams.FairnessOption.equals("")  && !explicitNof)
        {
            PcalParams.FairnessOption = "wf";

        }

        /********************************************************************
         * If we are processing the command-line arguments, we need to get  *
         * the input-file name.  Otherwise, we're done.                     *     
         *******************************************************************/
        if (inFile)
        {
            return STATUS_OK;
        }

        /********************************************************************
        * Set PcalParams.TLAInputFile to the last argument, removing a      *
        * "tla" extension if it has one.                                    *
        ********************************************************************/
        /*
        int dotIndex = args[maxArg].lastIndexOf(".") ;
        if (dotIndex == -1) 
        { 
          PcalParams.TLAInputFile = args[maxArg]; 
        } 
        else if (args[maxArg].substring(dotIndex).equals(".tla"))
        { 
          PcalParams.TLAInputFile = args[maxArg].substring(0, dotIndex); 
        }
        else 
        {  
          return CommandLineError("Input file has extension other than tla"); 
        }
        */

        // SZ 02.16.2009: check for correct file extension (ignoring case)
        // and file existence. also handles dots in the pathname
        File file = new File(args[maxArg]);
        boolean hasExtension = false;
        if (file.getName().lastIndexOf(".") == -1)
        {
            // no extension
            PcalParams.TLAInputFile = file.getPath();
        } else
        {
            // extension present
            if (file.getName().toLowerCase().endsWith(".tla"))
            {
                hasExtension = true;
            }
            // Aborted version 1.31 code
            // else if (file.getName().toLowerCase().endsWith(".pcal")){
            // hasExtension = true;
            // PcalParams.fromPcalFile = true;
            // }
            else
            {
                return CommandLineError("Input file has extension other than " /* pcal or */+ "tla");
            }
        }
        if (hasExtension)
        {
            // cut the extension
            PcalParams.TLAInputFile = file.getPath().substring(0, file.getPath().lastIndexOf("."));
            if (!file.exists())
            {
                return CommandLineError("Input file " + file.getPath() + " does not exist.");
            }
        } else
        {
            // aborted version 1.31 code
            // file = new File(PcalParams.TLAInputFile + ".pcal");
            // if (file.exists())
            // {
            // PcalParams.fromPcalFile = true;
            // } else
            // {
            file = new File(PcalParams.TLAInputFile + ".tla");
            if (!file.exists())
            {
                return CommandLineError("Input file " + PcalParams.TLAInputFile + ".pcal and " + file.getPath()
                        + ".tla not found");
            }
            // }
        }
        // file = new File(PcalParams.TLAInputFile + (PcalParams.fromPcalFile?".pcal":".tla"));
        // if (!file.exists())
        // {
        // return CommandLineError("Input file " + file.getPath() + " not found");
        // }

        return STATUS_OK;
    }

    /**
     * Prints out the help message
     * @return status if it has been successfully printed
     */
    private static boolean OutputHelpMessage()
    {
        Vector helpVec = null;
        try
        {
            helpVec = PcalResourceFileReader.ResourceFileToStringVector("help.txt");
        } catch (PcalResourceFileReaderException e)
        {
            PcalDebug.reportError(e);
            return false;
        }
        int i = 0;
        while (i < helpVec.size())
        {
            ToolIO.out.println((String) helpVec.elementAt(i));
            i = i + 1;
        }

        return true;
    }

    /**
     * Returns if the options are conflicting
     * @return true if the provided options are conflicting, false otherwise
     */
    private static boolean CheckForConflictingSpecOptions()
    {
        if ((PcalParams.SpecOption ? 1 : 0) + (PcalParams.MyspecOption ? 1 : 0) + (PcalParams.Spec2Option ? 1 : 0)
                + (PcalParams.Myspec2Option ? 1 : 0) + (PcalParams.WriteASTFlag ? 1 : 0) > 1)
        {
            CommandLineError("\nCan have at most one of the options " + "-spec, -myspec, -spec2, -myspec2, writeAST");
            return true;
        }
        ;
        return false;
    }

    private static int CommandLineError(String msg)
    /*********************************************************************
    * Announce a command line error with the string indicating the       *
    * explanation and halt.                                              *
    *********************************************************************/
    {
          PcalDebug.reportError("Command-line error: " + msg + ".");
//        ToolIO.out.println("Command-line error: " + msg + ".");
//        ToolIO.out.println("Use -help option for more information.");
        return STATUS_EXIT_WITH_ERRORS;
    }

    private static int findTokenPair(Vector vec, int lineNum, String tok1, String tok2)
    /*********************************************************************
    * Returns the number of the first line at or after lineNum in the    *
    * vector of strings vec containing tok1 followed by 1 or more        *
    * spaces followed by tok2.  Returns -1 if such a line is not found.  *
    *********************************************************************/
    {
        int i = lineNum;
        while (i < vec.size())
        {
            String line = (String) vec.elementAt(i);
            int col = line.indexOf(tok1);
            int nextcol = col + tok1.length();
            if (col != -1)
            {
                while ((nextcol < line.length()) && (line.charAt(nextcol) == ' '))
                {
                    nextcol = nextcol + 1;
                }
                ;
                if ((nextcol < line.length()) && (nextcol == line.indexOf(tok2)))
                {
                    return i;
                }
            }
            ;
            i = i + 1;
        }
        ;
        return -1;
    }

    /**************************  RemoveTabs  *********************************/

    public static Vector removeTabs(Vector vec)
    {
        /********************************************************************
        * Returns a string vector obtained from the string vector vec by   *
        * replacing any evil tabs with the appropriate number of spaces,   *
        * where "appropriate" means adding from 1 to 8 spaces in order to  *
        * make the next character fall on a column with Java column        *
        * number (counting from 0) congruent to 0 mod 8.  This is what     *
        * Emacs does when told to remove tabs, which makes it good enough  *
        * for me.                                                          *
         ********************************************************************/
        Vector newVec = new Vector();
        int i = 0;
        while (i < vec.size())
        {
            String oldline = (String) vec.elementAt(i);
            String newline = "";
            int next = 0;
            while (next < oldline.length())
            {
                if (oldline.charAt(next) == '\t')
                {
                    int toAdd = 8 - (newline.length() % 8);
                    while (toAdd > 0)
                    {
                        newline = newline + " ";
                        toAdd = toAdd - 1;
                    }
                } else
                {
                    newline = newline + oldline.substring(next, next + 1);
                }
                ;
                next = next + 1;
            }
            newVec.addElement(newline);
            i = i + 1;
        }
        ;
        return newVec;
    }

    /********************* STRING UTILITY FUNCTIONS ***********************/

    private static int NextSpace(String s, int cur)
    /********************************************************************
    * Returns the first space in s at or after col. If there is none,   *
    * return the index of the last character in s. Spaces in strings    *
    * are not treated as spaces. Assumes s[cur] is not in a string.     *
    ********************************************************************/
    {
        int i = cur;
        boolean inString = false;
        while ((i < s.length()) && ((s.charAt(i) != ' ') || inString))
        {
            if ((s.charAt(i) == '"') && ((i == 0) || (s.charAt(i - 1) != '\\')))
                inString = !inString;
            i = i + 1;
        }
        if (i == s.length())
            return i - 1;
        else
            return i;
    }

    private static String WrapString(String inString, int col)
    /*********************************************************************
    * Returns the string inString with lines wrapped approximately at    *
    * col, taking care not to wrap in a string.                          *
    *********************************************************************/
    {
        int i = 0;
        int ccol = 1;
        StringBuffer sb = new StringBuffer();
        while (i < inString.length())
        {
            if (inString.charAt(i) == ' ') // An initial space or a space
            {
                sb.append(' '); // that follows a space. It
                i = i + 1; // can always be appended to a line.
                ccol = ccol + 1;
            } else
            // Find next word, which starts at i.
            {
                int j = NextSpace(inString, i);
                if (ccol + (j - i + 1) > col)
                {
                    sb.append('\n');
                    ccol = 1;
                }
                while (i <= j) // If this overflows col, then the word
                {
                    sb.append(inString.charAt(i));
                    // is longer than col.
                    i = i + 1;
                    ccol = ccol + 1;
                }
            }
        }
        return sb.toString();
    }

}
