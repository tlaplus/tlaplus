/**
 * 
 */
package org.lamport.tla.toolbox.util;

/**
 * Contains some useful methods for manipulating strings.
 * 
 * @author lamport
 *
 */
public class StringHelper
{
    
    /*
     * The following defines newline to be a new-line character in whatever
     * system this is.
     */
    public static String newline = System.getProperty("line.separator");

    /**
     * Returns the result of concatenating 'copies' copies of string str, 
     * or the empty string if copies < 0. 
     */
    /*
     * It uses the  following algorithm, which produces a sequence of 1s
     * of length 'copies'.
     * 
     * --algorithm copy {
     * variables copies \in -5..100,        \* input: The number of repetitions
     *           result = << >>,            \* set to the output
     *           powerOf2Copies = << 1 >>,  \* 2^k copies of the input, for some k
     *           remaining = copies ;       \* see the invariant in the assert statement
     *   { while (remaining > 0) 
     *       {  assert copies = remaining * Len(powerOf2Copies) + Len(result) ;
     *          if (remaining % 2 # 0) { result := result \o powerOf2Copies };
     *          remaining := remaining \div 2;
     *          if (remaining # 0) {powerOf2Copies := powerOf2Copies \o powerOf2Copies ;} ;
     *       };
     *     assert (copies > 0) => (copies = Len(result)) ;
     *   }
     * }
     */
    public static final String copyString(String str, int copies) {
        String result = "";
        String powerOf2Copies = str;
        int    remaining = copies;
        while (remaining > 0) {
            if (remaining %2 != 0) {
                result = result + powerOf2Copies;
            }
            remaining = remaining / 2;
            if (remaining != 0) {
                powerOf2Copies = powerOf2Copies + powerOf2Copies;
            }
        }
        return result;
    }
    
    
    /**
     *  Returns true if the string str contains only whitespace 
     */
    public static final boolean onlySpaces(String str) {
        return str.trim().equals("");
    }
    
    /**
     * Returns str with any leading whitespace removed. 
     */
    public static final String trimFront(String str) {
        int position = 0;
        while ((position < str.length()) && 
                Character.isWhitespace(str.charAt(position))) {
          position++;
        }
        return str.substring(position, str.length());
        
        // Alternatively
        //return s.replaceAll("^\\s+", "");
    }
    
    /**
     * Returns str with any terminating whitespace removed. 
     */
    public static final String trimEnd(String str) {
        int position = str.length();
        while ((position > 0) && 
                Character.isWhitespace(str.charAt(position - 1))) {
          position--;
        }
        return str.substring(0, position);
        
        // Alternatively
        //return s.replaceAll("\\s+$", "");
    }
    
    /**
     * Returns the number of leading spaces in the string str.
     * @param str
     * @return
     */
    public static final int leadingSpaces(String str) {
        return str.length() - trimFront(str).length() ;
    }
    
    /**
     * Prints the elements of the array, one per line, enclosed between
     * *- and -*, except with the first line enclosed with 0- and -0.
     */
    public static final void printArray(Object[] array) {
        if (array == null) {
            System.out.println("null array");
            return;
        }
        if (array.length == 0) {
            System.out.println("zero-length array");
            return;
        }
        System.out.println("0-" + array[0].toString() + "-0");
        for (int i = 1; i < array.length; i++) {
            System.out.println("*-" + array[i].toString() + "-*");
        }
    }
        
    /**
     * Returns the sequence of words contained in str, where
     * a word is any sequence of non-space characters.
     * @param str
     * @return
     */
    public static final String[] getWords(String str) {
        String[] result = trimFront(str).split("\\s+") ;
        return result;
    }
    
    /**
     * Returns true iff str is a sequence of letters, "_" characters, and digits
     * that is not all digits.  
     * 
     * @param str
     * @return
     */
    public static final boolean isIdentifier(String str) {
        
        boolean result = true ;
        boolean allChars = true ;
        int i = 0;
        while (result && (i < str.length())) {
            char ch = str.charAt(i) ;
            result = Character.isLetterOrDigit(ch) || (ch == '_') ;
            allChars = allChars && Character.isDigit(ch) ;
            i++;
        }
        return result && (! allChars) ;
    }
}
