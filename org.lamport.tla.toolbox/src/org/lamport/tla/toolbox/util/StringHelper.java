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
    /*
     * This implementation was the result of testing what
     * String.split does.  The documentation doesn't
     * give a clue.
     */
    public static final String trimFront(String str) {
        String[] split = str.split("\\s*", 2);
        if (split.length < 2) {return "" ; }
        return split[1];
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
}
