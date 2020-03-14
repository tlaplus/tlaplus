/***************************************************************************
* CLASS PcalCharReader                                                     *
*                                                                          *
* A PcalCharReader is an input stream that can be read one character at a  *
* time.  The class's constructor produces such a stream from a vector of   *
* strings and starting and ending positions within the vector.  The        *
* reader expands tabs into spaces.  A PcalCharReader object has the        *
* following public methods.                                                *
*                                                                          *
* char getNextChar()    : Returns the next input character, or '\t' if     *
*                         there is none.                                   *
*                                                                          *
* int getLineNumber()   : Returns the line number of the next char to be   *
*                         returned by getNextChar().                       *
*                                                                          *
* int getColumnNumber() : Returns the column number of the next char to    *
*                         be returned by getNextChar().                    *
*                                                                          *
* backspace() :                                                            *
*    Backspaces the stream by one character.  Does not work right          *
*    if this backspaces over a tab character.                              *
*                                                                          *
* String peek() ;                                                          *
*    Moves the input stream to the next non-space character, then          *
*    returns the string from that character to the end of the line         *
*    including the "\n".  (It leaves the input stream at that              *
*    non-space character.)  It returns "\t" if it comes to the             *
*    end of the input stream.                                              *
*                                                                          *
* Lines and columns are numbered starting from 0.                          *
***************************************************************************/
package pcal;
import java.util.Vector;

class PcalCharReader 
  { /***********************************************************************
    * The variables representing the state of the object.                  *
    ***********************************************************************/
    private Vector vec ;
      /*********************************************************************
      * This is the vector providing the input characters.                 *
      *********************************************************************/

    private String currentLine = null ;
      /*********************************************************************
      * The current line of input, or null if at the end of the input.     *
      *********************************************************************/

    protected int line  = 0;                
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

    private int lastLine   = 0 ;
    private int lastColumn = 0 ;
      /*********************************************************************
      * These values marks the position in the input vector immediately    *
      * following the last character in the input stream.                  *
      *********************************************************************/

    private boolean tabToSpaces = false ;
      /*********************************************************************
      * Equals true when a tab has been encountered in the input stream,   *
      * and the next getNextChar should return a space generated from      *
      * that tab.                                                          *
      *********************************************************************/

    /***********************************************************************
    * The methods.                                                         *
    ***********************************************************************/
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
      { /*******************************************************************
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

       /********************************************************************
       * If the current position equals the final position, return '\t'.   *
       ********************************************************************/
       if (    (line > lastLine) 
            || ( (line == lastLine) && (column >= lastColumn) ) )
         { return '\t' ; }

        /*******************************************************************
        * If the current column is at the end of the current line, then    *
        * return '\n' after updating the line and column and reading in    *
        * the next line.                                                   *
        *********************************************************************/
        if (currentLine.length() == column) 
          { line        = line + 1 ;
            column      = 0 ;
            vcolumn     = 0 ;
            if (line >= vec.size())
                 {currentLine = null ;}
            else {currentLine = (String) vec.elementAt(line) ;} ;
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
      * line.                                                              *
      *                                                                    *
      * Incorrect results will occur if backspacing over a tab character.  *
      * (This could be corrected, but it's not needed, and getting it      *
      * right is tricky.)                                                  *
      *                                                                    *
      * This method allows backspacing beyond the logical beginning        *
      * of the reader, as specified by the firstLine and firstCol          *
      * arguments to the constructor.                                      *
      *********************************************************************/
      { if (column == 0)
         { if (line == 0)
             { PcalDebug.ReportBug(
                  "PcalCharReader.backspace trying to " +
                  "move past beginning of reader");
             } ;
           line = line - 1 ;
           currentLine = (String) vec.elementAt(line) ;
           column = 0 ;
           vcolumn = 0 ;

           /****************************************************************
           * Need to move forward from the first character of the line in  *
           * case there are tabs.                                          *
           ****************************************************************/
           while (column < currentLine.length() - 1)
             { char c = getNextChar() ; }
         }
        else
         { column = column - 1;
           vcolumn = vcolumn - 1;
         }
      } ;

    public String peek()
      /***************************************************************
      * Moves the input stream to the next non-space character,      *
      * then returns the string from that character to the end of    *
      * the line including the "\n".  (It leaves the input stream    *
      * at that non-space character.)  It returns "\t" if it comes   *
      * to the end of the input stream.                              *
      ***************************************************************/
      { 
// System.out.println("Peek called at line = " + line + ", col = " + column);
        char next = getNextChar() ;
        while (   (next == ' ')
               || (next == '\n'))
           { next = getNextChar() ;} ;
        if (next == '\t')
          { return "\t" ;} ;
        backspace() ;
// System.out.println("Peek returns `" +  currentLine.substring(column) + "' at line = " + line + ", col = " + column);
        return currentLine.substring(column) + "\n" ;
      }
      
    public PcalCharReader(Vector vector, int firstLine, int firstCol,
                            int lastLine, int lastCol) 
      /*********************************************************************
      * The class constructor.  The only tricky part is setting vcolumn    *
      * to account for tabs on the same line but before the starting       *
      * point.                                                             *
      *********************************************************************/
      { this.vec         = vector ;
        this.line        = firstLine ;
        this.column      = firstCol ;
        this.lastLine    = lastLine ;
        this.lastColumn  = lastCol ;
        /*******************************************************************
        * Compute the initial value of vcolumn.                            *
        *******************************************************************/
        if (firstLine < vector.size())
          { int i = 0 ;
            String ln = (String) vector.elementAt(firstLine) ;
            while (i < firstCol)
             { if (ln.charAt(i) == '\t')
                 { this.vcolumn = ((this.vcolumn / 8) + 1) * 8 ;}
               else {this.vcolumn = this.vcolumn + 1 ; } ;
               i = i + 1;
             }
          } ;

        /*******************************************************************
        * Set currentLine.                                                 *
        *******************************************************************/
        if (firstLine < vector.size())
          { this.currentLine = (String) vector.elementAt(firstLine) ; } ;
      } ;
  }     
