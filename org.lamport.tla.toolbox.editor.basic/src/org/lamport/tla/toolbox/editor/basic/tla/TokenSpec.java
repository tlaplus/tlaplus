/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.tla;

/**
 * A TokenSpec object represents a possible TLA+ symbol name together
 * with the position of that symbol in a line of text.  Note that the
 * expression Foo(a, b)!Bar(c) may be an occurrence of the symbol
 * named "Foo!Bar", whose left position is at the "F" and whose right
 * position is just after the "r" (and hence, at the following ")").
 * 
 * The main method is findTokenSpecs.
 *  
 * @author lamport
 *
 */
public class TokenSpec
{
    /*
     * The following are the fields of the object.  They are accessed
     * directly, without any of this set...() and get...() Java 
     * nonsense.
     */
    public String token;
    public int leftPos;
    public int rightPos;

    public TokenSpec(String tok, int left, int right)
    {
        this.token = tok;
        this.leftPos = left;
        this.rightPos = right;
    }

    /** 
     * This method finds all possible symbol names containing the character at
     * or just before position inputPosition of line inputLine, in order of
     * decreasing length.  There can be multiple possibilities because if
     * inputPosition is at the "a" in
     * 
     *    Foo!Bar!End
     * 
     * then the method return the array whose first element represents
     * Foo!Bar!End and whose second element represents Foo!Bar.  We don't
     * know which is correct, because End could either be a symbol defined
     * in an instantiated instantiated model, or else a label in the 
     * definition of the instantiated symbol Bar.
     * 
     * This method is the encoding of the PlusCal procedure of the same name in
     * module FindOp, which is appended as a comment to this file.
     * 
     * @param inputLine
     * @param inputPosition
     * @return
     */
    public static TokenSpec[] findTokenSpecs(String inputLine, int inputPosition)
    {
        // we pad the input line on the ends so we don't have to worry
        // about going off the end of the line.
        String line = Padding + inputLine + Padding;

        // Maintains the current position at which we are processing.
        int curPos = inputPosition;

        // Contains the result we've found so far.
        TokenSpec[] foundTokenSpecs = new TokenSpec[0];

        // Set true if there can be no tokens to right of first one found.
        boolean lastToken = false;

        // Set true if we find a "!" to the right of the first token found.
        boolean notLastToken = false;

        
        System.out.println("Started");
        for (int i = Padding.length(); i < line.length() - Padding.length(); i++)
        {
//            TokenSpec ts = findMaximalIdCharSeq(line, i);
//            if (ts != null)
//                System.out.println("" + i + ": " + ts.toString());
            System.out.println("" + i + ": " + findMatchingRightParen(line, i));
        }
        System.out.println("Finisheded");

        return null;
    }


    /**
     *  Returns the TokenSpec for the token in the array tokArray of Java
     * strings (Java array of 1-character strings) in the line containing the
     * character at position pos, or NullTokenSpec if there is none.
     * 
     * @return
     */
    private static TokenSpec findTokenIn(String line, int pos, String[] tokArray)
    {
        int tokIdx;
        for (int i = 0; i < tokArray.length; i++)
        {
            tokIdx = tokArray[i].indexOf(line.charAt(pos), 0);
            while (tokIdx != -1)
            {
                int ftlft = pos - tokIdx;
                int ftrt = pos - tokIdx + tokArray[i].length();
                if (tokArray[i].equals(line.substring(ftlft, ftrt)))
                {
                    return new TokenSpec(tokArray[i], ftlft, ftrt);
                }
                tokIdx = tokArray[i].indexOf(line.charAt(pos), tokIdx + 1);
            }
        }
        return null;
    }

    /**
     * Returns the TokenSpec of the largest token containing digits, letters,
     * and "_" characters containing position pos.  Returns null if
     * that would be an empty token.
     */
    private static TokenSpec findMaximalIdCharSeq(String line, int pos)
    {
        int left = pos;
        int rt = pos;
        left = pos;
        while (Character.isLetterOrDigit(line.charAt(left - 1)) || line.charAt(left - 1) == '_')
        {
            left--;
        }
        while (Character.isLetterOrDigit(line.charAt(rt)) || line.charAt(left - 1) == '_')

        {
            rt++;
        }
        if (left == rt)
        {
            return null;
        } else
        {
            return new TokenSpec(line.substring(left, rt), left, rt);
        }
    }

    /**
     * Returns the position of the left paren matching a ")" at pos-1.  
     * If there is none, it returns -1.
     * 
     * @param line
     * @param pos
     * @return
     */
    private static int findMatchingLeftParen(String line, int pos) 
    { if (line.charAt(pos-1) != ')') {return pos; };
      return findMatchingLeftInner(line, pos, 0);
     }

    private static int findMatchingLeftInner(String line, int pos, int delim) 
    { int ipos = pos; 
      int jdelim; 
      int delimLen = LeftDelimiters[delim].length();
      ipos = pos - delimLen;
      while ( ! line.substring(ipos-delimLen, ipos).equals(LeftDelimiters[delim]))
       { if (line.charAt(ipos-1) == PaddingChar) {return -1; };
         ipos = ipos-1;
         jdelim = 0;
         while (jdelim < LeftDelimiters.length)
          { if (line.substring(ipos-delimLen, ipos).equals(RightDelimiters[jdelim]))
             { ipos = findMatchingLeftInner(line, ipos, jdelim);
               if (ipos < 0) { return -1; }
               jdelim = 99999 ; // exit while loop
             };
            jdelim = jdelim+1;
          }
       };
       return ipos-delimLen;
     }

    /**
     * Returns the position of the right paren matching a "(" at position pos.  
     * If there is none, it returns -1.
     * 
     * @param line
     * @param pos
     * @return
     */
    private static int findMatchingRightParen(String line, int pos) 
    { if (line.charAt(pos) != '(') {return pos; };
      return findMatchingRightInner(line, pos, 0);
     }

    private static int findMatchingRightInner(String line, int pos, int delim) 
        { int ipos = pos; 
          int jdelim; 
          int delimLen = RightDelimiters[delim].length();
          ipos = pos + delimLen;
         while ( ! line.substring(ipos, ipos+delimLen).equals(RightDelimiters[delim]))
          { if (line.charAt(ipos) == PaddingChar) {return -1; }
            ipos = ipos+1;
           jdelim = 0;
           while (jdelim < RightDelimiters.length)
          { if (line.substring(ipos, ipos+delimLen).equals(LeftDelimiters[jdelim]))
             { ipos = findMatchingRightInner(line, ipos, jdelim);
               if (ipos < 0) { return -1; }
               jdelim = 99999 ; // exit while loop
             };
            jdelim = jdelim+1;
          }
       };
       return ipos+delimLen ;
     }

    private static int skipLeftOverSpaces(String line, int curPos)
    {
        int index = curPos;
        while (line.charAt(index - 1) == ' ')
        {
            index--;
        }
        return index;
    }

    private static int skipRightOverSpaces(String line, int curPos)
    {
        int index = curPos;
        while (line.charAt(index) == ' ')
        {
            index++;
        }
        return index;
    }

    private static char PaddingChar = '\u0000';

    private static String Padding = "" + PaddingChar + PaddingChar + PaddingChar + PaddingChar + PaddingChar
            + PaddingChar + PaddingChar + PaddingChar + PaddingChar + PaddingChar;

    private static String[] XOperators = { "(\\X)", "\\X" };
    
    private static String[] RightDelimiters = { ")", "]", "}", ">>" };
    private static String[] LeftDelimiters  = { "(", "[", "{", "<<" };


    public String toString()
    {
        return "[token |-> " + this.token + ", leftPos |-> " + this.leftPos + ", rightPos |-> " + this.rightPos + "]";
    }

    private class State
    {

    }

}
