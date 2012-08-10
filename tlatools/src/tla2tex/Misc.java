// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS Misc                                                               *
*                                                                          *
* Miscellaneous static methods (aka procedures).                           *
*                                                                          *
*                                                                          *
* stringToFloat : Converts a String to a float.                            *
*                                                                          *
* BreakStringOut                                                           *
*    Writes a string to an OutputFileWriter, splitting long lines          *
*    at spaces.                                                            *
*                                                                          *
* WriteIfNonNull                                                           *
*    Calls BreakStringOut to write a string, if it's not null.             *
*                                                                          *
* EliminateLeadingBlanks                                                   *
*    Removes leading spaces from a string.                                 *
*                                                                          *
* TeXify                                                                   *
*    Replace LaTeX's special characters in the string with LaTex           *
*    commands to produce them.                                             *
*                                                                          *
* TeXifyIdent                                                              *
*    Replaces each "_"  by a "\_" command in a string.                     *
*                                                                          *
* BreakLine                                                                *
*    Replaces each tab in the string by a space or a "\n", to break the    *
*    string into short lines for printing.  Useful for printing messages   *
*    or debugging output.                                                  *
*                                                                          *
* IsLetter                                                                 *
*    Tests if a char is a letter or "_".                                   *
*                                                                          *
* IsDigit                                                                  *
*    Tests if a char is a digit.                                           *
*                                                                          *
* IsLowerCase                                                              *
*    Tests if a string consists entirely of lower-case letters.            *
*                                                                          *
* IsUpperCase                                                              *
*    Tests if a string consists entirely of upper-case letters.            *
*                                                                          *
* IsCapitalized                                                            *
*    Tests if a string consists of an upper-case letter followed           *
*    by a string of lower-case letters.                                    *
***************************************************************************/
package tla2tex;

public final class Misc
{  public static float stringToFloat(String str)
     /**********************************************************************
     * Converts a string such as "123.456", ".123", "123.", or "123" to a  *
     * float.  (Lord knows why the standard Java libraries don't provide   *
     * such a method.)                                                     *
     **********************************************************************/
     { int pointPos = str.indexOf(".");
       if (pointPos == -1)
         { Debug.Assert(str.length() > 0, 
                  "stringToFloat called with empty string");
           if (str.length() > 18)
              { String substr = str.substring(0,18) ;
                float multiplier = 1;
                float exponent = str.length() - 18;
                while (exponent > 0)
                 { multiplier = multiplier * 10 ;
                   exponent = exponent - 1;
                 } ;
                return ((float) Long.parseLong(substr)) * multiplier ;
              } ;
            return (float) Long.parseLong(str); 
         } ;
       String strMinusPoint 
         = str.substring(0,pointPos) + str.substring(pointPos + 1) ;
       Debug.Assert(strMinusPoint.length() > 0, 
                  "stringToFloat called with the string \".\"");
       if (strMinusPoint.length() > 18)
         { strMinusPoint = strMinusPoint.substring(0,18);};
       long divisor = 1;
       long exponent = strMinusPoint.length() - pointPos;
       while (exponent > 0)
        { divisor = divisor * 10 ;
          exponent = exponent - 1;
        } ;
      return ((float) Long.parseLong(strMinusPoint)) / divisor ;
     } ;

  public static String floatToString(float f, int d)
    /***********************************************************************
    * Converts the float f to a string of the form "xxx.yyyyy", where the  *
    * number of digits in yyyyy is at most d.                              *
    ***********************************************************************/
    { String fStr = "" + f;
      int ePos = fStr.indexOf("E");
      int shiftRight = 0 ;
      int ptPos;
      float tenToTheMinusD = 1;
      int i = d ;
      while (i > 0)
       { tenToTheMinusD = tenToTheMinusD / 10 ;
         i = i-1 ;
       } ;
      if (f <= tenToTheMinusD) {return "0";} ;
      if (ePos != -1)
        { shiftRight = Integer.parseInt(fStr.substring(ePos + 1));
          fStr = fStr.substring(0, ePos);
          ptPos = fStr.indexOf(".") ;
          fStr = fStr.substring(0, ptPos) + fStr.substring(ptPos + 1);
          ptPos = ptPos + shiftRight ;
          while (ptPos < 0)
           { fStr = "0" + fStr;
             ptPos = ptPos + 1;
           } ;
          while (ptPos > fStr.length())
           { fStr = fStr + "0" ;
           } ;
          if (ptPos != fStr.length())
           { fStr = fStr.substring(0, ptPos) + "." + fStr.substring(ptPos);
           }
        } ; // END if (ePos != -1)
      ptPos = fStr.indexOf(".") ;
      if (ptPos == -1) {return fStr;}
      while (fStr.length() - ptPos > d+1)
       { fStr = fStr.substring(0, fStr.length()-1); }
      return fStr ;      
    }

  public static void WriteIfNonNull(OutputFileWriter writer, String str)
    /***********************************************************************
    * If str is non-empty, write it to writer, breaking long lines.        *
    ***********************************************************************/
    { if (! str.equals(""))
        { BreakStringOut(writer, str); }
    }



  public static void BreakStringOut(OutputFileWriter output, String str)
  /*************************************************************************
  * Writes str to output, trying to limit the length of output lines by    *
  * breaking the string at spaces into separate lines.                     *
  *************************************************************************/
  { String restOfString = str ;
    String nextLine = "" ;
    boolean done = false ;
    boolean cut = false ;
    while (   (!done) 
           && (restOfString.length() > Parameters.MaxOutputLineLength))
     { /********************************************************************
       * If there is a space char in the line, set lastSpace to the index  *
       * of the char at which to break the line: either the last space     *
       * char before index MaxOutputLineLength, or the first one after     *
       * it.  If there is no space char in the line, set lastSpace to -1.  *
       ********************************************************************/
       int lastSpace = restOfString.lastIndexOf(' ', 
                          Parameters.MaxOutputLineLength - 1);

       if (lastSpace == -1)
        { lastSpace = restOfString.indexOf(' ');
        };

       if (lastSpace <= Parameters.MaxOutputLineLength / 4)
        { done = true ; 
        }
       else
        { /*****************************************************************
          * There is a line break possible.  Set outputLine to the line    *
          * to be output and restOfString to the rest.                     *
          *****************************************************************/
          cut = true ;
          String outputLine = 
              EliminateLeadingBlanks(restOfString.substring(0, lastSpace)) ;
          restOfString = restOfString.substring(lastSpace);
          if (! outputLine.equals(""))
            { output.putLine(" " + outputLine);
            } ;
        } ;
     };
    if (cut)
      { restOfString = EliminateLeadingBlanks(restOfString) ;
        if (! restOfString.equals(""))
         { output.putLine(" " + restOfString); };
      } 
    else
     { output.putLine(restOfString); 
     };
  }  

  public static String EliminateLeadingBlanks(String str)
    /***********************************************************************
    * Equals str with leading blanks removed.                              *
    ***********************************************************************/
    { int firstNonBlank = 0 ;
      while (   (firstNonBlank < str.length())
             && (str.charAt(firstNonBlank) == ' '))
        { firstNonBlank = firstNonBlank + 1; } ;
      return str.substring(firstNonBlank) ;
    }
    
  public static String TeXify(String str)
    /***********************************************************************
    * Result is str with each of TeX's special characters replaced by the  *
    * command to produce it.                                               *
    ***********************************************************************/
    { String result = "" ;
      int pos = 0 ;
      while (pos < str.length())
       { switch (str.charAt(pos))
           { case '_' :
               result = result + "\\_" ;
               break ;
             case '{' :
               result = result + "\\{" ;
               break ;
             case '}' :
               result = result + "\\}" ;
               break ;
             case '\\' :          
               result = result + "\\ensuremath{\\backslash}" ;
               break ;
             case '&' :
               result = result + "\\&" ;
               break ;
             case '%' :
               result = result + "\\%" ;
               break ;
             case '$' :
               result = result + "\\$" ;
               break ;
             case '#' :
               result = result + "\\#" ;
               break ;
             case '~' : 
               result = result + "\\ensuremath{\\sim}" ;
               break ;
             case '^' :
               result = result + "\\ensuremath{\\ct}" ;
               break ;
             case '<' :
               result = result + "\\ensuremath{<}" ;
               break ;
             case '>' :
               result = result + "\\ensuremath{>}" ;
               break ;
             case '|' :          
               result = result + "\\ensuremath{|}" ;
               break ;
             default :
               result = result + str.charAt(pos) ;
            } ;
        pos = pos + 1 ;
       } ;
      return result ;
    }    

  public static String TeXifyIdent(String str)
    /***********************************************************************
    * Result is str with each occurrence of "_" replaced by a \\_ command. *
    ***********************************************************************/
    { String out = str ;
      int nextUS = str.indexOf("_");
      while (nextUS != -1)
       { 
         if (nextUS == 0)
          { out = "\\" + out;
          }
         else
          { out = out.substring(0, nextUS) + "\\_" + out.substring(nextUS+1);
          } ;
         nextUS = out.indexOf("_", nextUS + 2) ;
       };
      return out ;
    }

  /**
   * The LaTeX output for producing a label.  As a first attempt, here is
   * the algorithm:
   * 
   *    - typeset the Ident part of the label as in TeXifyIdent.
   *    - add \@s{.5} or \@s{2.5} depending on whether or not there
   *      is one or more spaces before the ":"
   *    - put the ":", ":+", or ":-" in a \textrm command, eliminating
   *      any spaces.
   *    - add \@s{3} or @s{4} depending on whether there are spaces before
   *      the ":"
   * @param str
   * @return
   */
  public static String TeXifyPcalLabel(String str) {
      String out = "";
      int next = 0 ;
      while (    (next < str.length())
              && (   IsLetter(str.charAt(next))) 
                  || IsDigit(str.charAt(next))) {
          char nextChar = str.charAt(next) ;
          next++ ;
          if (nextChar == '_') {
              out = out + "\\" ;
          } 
          out = out + nextChar ;
      }
      int numberOfSpaces = 0 ;
      while (next < str.length() && IsSpace(str.charAt(next))) {
          numberOfSpaces++ ;
          next++ ;
      }
      if (numberOfSpaces == 0) {
          out = out + "\\@s{.5}" ;
      }
      else {
          out = out + "\\@s{2.5}" ;
      }
      out = out + "\\textrm{" ;
      while (next < str.length()) {
          char nextChar = str.charAt(next) ;
          next++ ;
          if (! IsSpace(nextChar)) {
              out = out + nextChar ;
          }
      }
      out = out + ((numberOfSpaces == 0) ? "}\\@s{3}" : "}\\@s{4}") ;
      return out;
  }

  private static final int MAXLEN = 48;
    /***********************************************************************
    * The maximum output line length for the BreakLine method.             *
    ***********************************************************************/
    
  public static String BreakLine(String str)
  /*************************************************************************
  * Used for printing output with reasonable line breaks.  The argument    *
  * str is a string with '\t' characters.  The method returns str with     *
  * each '\t' character either removed or replaced by a '\n' if the        *
  * current line of the result string has more than MAXLEN characters.     *
  **************************************************************************/
  { int lineLen = 0 ; 
    int nextChar = 0 ;
    String newStr = "" ;
    char ch = '0' ;
    while (nextChar < str.length())
      { ch = str.charAt(nextChar) ;
        if (ch == '\t')
          { if (lineLen > MAXLEN)
              { newStr = newStr + "\n       " ;
                lineLen = 7;
              }
          }
        else
          { newStr = newStr + ch;
            lineLen = lineLen + 1;
          } ;
        nextChar = nextChar + 1 ;
      };
    return newStr ;
   } ;

    public static boolean IsLetter(char c) 
      /*********************************************************************
      * True iff c is a letter or '_'.                                     *
      *********************************************************************/
      { return      ( ('a' <= c ) && (c <= 'z') )
                 || ( ('A' <= c ) && (c <= 'Z') )
                 || ( c == '_' ) ;} ;

                 
    public static boolean hasLetter(String str) {
       boolean notFound = true ;
       int i = 0 ;
       while (notFound && (i < str.length())) {
          if (IsLetter(str.charAt(i))) {
              notFound = false ;
          }
          i++ ;
       }
       return ! notFound ;
    }
    
    public static boolean IsDigit(char c) 
      /*********************************************************************
      * True iff c is a digit.                                             *
      *********************************************************************/
      { return ('0' <= c ) && (c <= '9'); } ;

    public static boolean IsSpace(char c) 
      /*********************************************************************
      * True iff c is a space character--that is, one of the following:    *
      * \f, \r, or ' '.  A \n is not considered a space character.         *
      *********************************************************************/
      { return  (c == ' ')  | (c == '\f') | (c == '\r') ; } ;


  public static boolean isBlank(String str) 
    /***********************************************************************
    * True iff str has nothing but space characters.                       *
    ***********************************************************************/
   { return str.trim().equals("") ;
   }

  public static boolean IsLowerCase(String str)
    /***********************************************************************
    * True iff str consists entirely of lower-case letters.                *
    ***********************************************************************/
    { int i = 0 ;
      boolean result = true ;
      while (   (i < str.length())
             && result)
       { char c = str.charAt(i);
         if (('a' >  c ) || ( c > 'z'))
           { result = false ; };
         i = i+1;
       }
      return result;
    }

  public static boolean IsUpperCase(String str)
    /***********************************************************************
    * True iff str consists entirely of upper-case letters.                *
    ***********************************************************************/
    { int i = 0 ;
      boolean result = true ;
      while (   (i < str.length())
             && result)
       { char c = str.charAt(i);
         if (('A' >  c ) || ( c > 'Z'))
           { result = false ; };
         i = i+1;
       }
      return result;
    }

  public static boolean IsCapitalized(String str)
    /***********************************************************************
    * True iff str consists of an upper-case letter followed by a          *
    * possibly null string of lower-case letters.                          *
    ***********************************************************************/
    { if (str.length() > 0)
       { char c = str.charAt(0);
         return  ('A' <= c ) && (c <= 'Z') && IsLowerCase(str.substring(1));
       } ;
      return false;
    }

}
