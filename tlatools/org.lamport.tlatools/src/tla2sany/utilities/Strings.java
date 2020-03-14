// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.utilities;

public class Strings {

  public static final String []  blanks = {""," ","| ","   ","| | ",
                                   "     ","| | | ","       ","| | | | " };

  // Inserts blanks into a string right after newline characters to create
  // indentation when printed.
  public static String indent(int n /* numb blanks to insert*/ , String ss) {

    String s = "";
    if (n >= blanks.length) n = blanks.length-1;

    for (int i=0; i < ss.length(); i++) {
      s += ss.charAt(i);
      if (ss.charAt(i) == '\n' && i!=ss.length()-1) {  // no blanks after terminal \n
        s += blanks[n];
      }
    } // end for
    return s;
  }

  // Same as above, but uses StringBuffer operations internally
  // Should be much faster for very large strings
  public static String indentSB(int n, String ss) {

    StringBuffer sb = new StringBuffer(ss.length()*2);

    if (n>=blanks.length) n = blanks.length-1;

    for (int i = 0; i < ss.length(); i++) {
      sb.append(ss.charAt(i));
      if (ss.charAt(i) == '\n' && i!=ss.length()-1) {  // no blanks after terminal \n
        sb.append(blanks[n]);
      }
    } // end for
    return sb.toString();
  } // end method

}
