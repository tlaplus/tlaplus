// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* ABSTRACT CLASS CharReader                                                *
*                                                                          *
* Provides an input stream that can be read one character at a time.  It   *
* expands tabs into spaces.  It provides the following methods.            *
*                                                                          *
* char getNextChar()    : Returns the next input character, or '\t' if     *
*                         there is none.                                   *
*                                                                          *
* void close()          : Closes the input stream.                         *
*                                                                          *
* int getLineNumber()   : Returns the line number of the next char to be   *
*                         returned by getNextChar().                       *
*                                                                          *
* int getColumnNumber() : Returns the column number of the next char to    *
*                         be returned by getNextChar().                    *
*                                                                          *
* Lines and columns are numbered starting from 0.                          *
*                                                                          *
* IMPLEMENTED BY FileCharReader.                                           *
***************************************************************************/
package tla2tex;

public abstract class CharReader 
  /*************************************************************************
  * This class provides a method for reading characters one at a time,     *
  * using the getNextChar method.  It is to be extended by a subclass      *
  * that defines (a) the method innerGetNextLine to return the next line   *
  * of actual input, and (b) the close method.                             *
  *************************************************************************/
  { /***********************************************************************
    * The variables representing the state of the object.                  *
    ***********************************************************************/

    private String currentLine = null ;
      /*********************************************************************
      * The current line of input, or null if at the end of the input or   *
      * before initialization (see below).                                 *
      *********************************************************************/

    private boolean uninitialized = true ;
      /*********************************************************************
      * Logically, we want to initialize currentLine to                    *
      * innerGetNextLine().  However, this doesn't work because the        *
      * CharReader class initialization is performed before any subclass   *
      * initialization, and the subclass has to be initialized for         *
      * innerGetNextLine() to work.  So, currentLine is initialized by     *
      * getNextChar the first time it is called, whereupon it sets         *
      * uninitialized to false.                                            *
      *********************************************************************/

    protected int line    = 0;                
    private int column  = 0;                
    private int vcolumn = 0;
      /*********************************************************************
      * The line and column numbers of the next character to be returned   *
      * by getNextChar, where column is the actual position of the next    *
      * character in the input stream, and vcolumn is what the column      *
      * number would be if tabs had been "expanded".  When columm =        *
      * length of currentLine, the next character to be returned is '\n'.  *
      *                                                                    *
      * In Java fashion, these are numbered starting at 0.                 *
      *********************************************************************/


    public int getLineNumber() 
      /*********************************************************************
      * Returns the line number of the next character to be returned by    *
      * getNextChar.  Following Java conventions, the first line is        *
      * numbered 0.                                                        *
      *********************************************************************/
      { return line ; } ;


    public int getColumnNumber() 
      /*********************************************************************
      * Returns the virtual column number of the next character to be      *
      * returned by getNextChar.  Following Java conventions, the first    *
      * column is numbered 0.                                              *
      *********************************************************************/
      { return vcolumn ; } ;

    private boolean tabToSpaces = false ;
      /*********************************************************************
      * Equals true when a tab has been encountered in the input stream,   *
      * and the next getNextChar should return a space generated from      *
      * that tab.                                                          *
      *********************************************************************/
      
    public char getNextChar()
      /*********************************************************************
      * Returns the next character in the input stream and updates the     *
      * line and column numbers.  However, it replaces each '\t' (tab) in  *
      * the input stream with the appropriate number of spaces (assuming   *
      * the standard "tab stops").  If the current column is after the     *
      * last character on the current line, then it returns '\n'.  If the  *
      * end of the input has been reached, then it returns '\t'.  Note     *
      * that, for a nonempty input stream, the call preceding the one      *
      * that returns '\t' must return '\n'.  For an empty input stream,    *
      * the first call returns '\t'.                                       *
      *********************************************************************/
      { if (uninitialized) {currentLine   = innerGetNextLine();
                            uninitialized = false; } ;
  
        /*******************************************************************
        * If currentLine is null, then we must have reached the end of the *
        * input.                                                           *
        *******************************************************************/
        if (currentLine == null) { return '\t' ;} ;
  
        /*******************************************************************
        * If we are converting a tab to spaces, return a space.            *
        *******************************************************************/
        if (tabToSpaces)
          { vcolumn = vcolumn + 1;
            if ((vcolumn % 8) == 0) {tabToSpaces = false;};
            return ' ';
          }

        /*******************************************************************
        * If the current column is at the end of the current line, then    *
        * return '\n' after updating the line and column and reading in    *
        * the next line.                                                   *
        *********************************************************************/
        if (currentLine.length() == column) 
          { line        = line + 1 ;
            column      = 0 ;
            vcolumn     = 0 ;
            currentLine = innerGetNextLine();
            return '\n' ;
           } ;
  
        /*******************************************************************
        * We are not at the end of the input or of the line and are not    *
        * converting a tab to space.  Update column and vcolumn, and       *
        * return the next character.                                       *
        *******************************************************************/
        char readChar = currentLine.charAt(column) ;
        column = column + 1;
        vcolumn = vcolumn + 1;
        if (readChar == '\t')
          { if ((vcolumn % 8) != 0) {tabToSpaces = true;} ;
            return ' ';
          }
        return readChar ;
      } ;

    public void backspace()
      /*********************************************************************
      * Backspaces the output stream.  That is, a sequence of n            *
      * backspaces without a getNextChar makes the next getNextChar        *
      * return the character returned by the n-th preceding getNextChar.   *
      * It is not possible to backspace past the first character in a      *
      * line.  Incorrect results will occur if backspacing over a tab      *
      * character.  (This could be corrected, but it's not needed for      *
      * TLATeX, and getting it right is tricky.)                           *
      *********************************************************************/
      { if (column == 0)
         { Debug.ReportBug(
            "CharReader.backspace trying to move past beginning of line");
         };
        column = column - 1;
        vcolumn = vcolumn - 1;
      } ;

    public abstract String innerGetNextLine() ;
      /*********************************************************************
      * The method innerGetNextLine is a method constructed from some      *
      * underlying reader class that returns the next line as a string,    *
      * or null if it's at the end of the input.                           *
      *********************************************************************/
    public abstract void close() ;  
      /*********************************************************************
      * This is the close method of the underlying reader class.           *
      *********************************************************************/
}     
