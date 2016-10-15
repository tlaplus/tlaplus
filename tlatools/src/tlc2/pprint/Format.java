// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:20:42 PST by lamport
//      modified on Wed Jun 16 14:35:25 EDT 1999 by tuttle
//      modified on Fri Jun 11 17:50:44 PDT 1999 by yuanyu

package tlc2.pprint;

public class Format {

/***************************************************************************/
/* This class provides a format method that accepts the parse tree for a   */
/* TLC value and returns a nicely-formatted version of the value.  The     */
/* value is split across as many lines as necessary for the value to fit   */
/* within a specified number of columns.                                   */
/***************************************************************************/

/***************************************************************************/
/* The following constants determine how each type of value should         */
/* be formatted.                                                           */
/*                                                                         */
/* Open and Close give the strings like "{" and "}" used as the opening    */
/* and closing delimters for a value like a set.                           */
/*                                                                         */
/* Pad gives the string appended to the left of lines two and higher to    */
/* indent the components of the value so that they line up correctly on    */
/* adjacent lines.  This should be a string of spaces with length equal    */
/* to the Open string.                                                     */
/*                                                                         */
/* Sep gives the string that should follow the component of a value to     */
/* separate it from the next component, like "," between elements of a     */
/* set or " @@" between pairs of values defining the function.             */
/*                                                                         */
/* Div gives the string like " |->" separating elements of pairs like the  */
/* name/value pairs defining a field in a record or like " :>" separating  */
/* the argument/value pairs defining a function.                           */
/*                                                                         */
/* DivPad gives the string appended to the left of lines containing the    */
/* second element of a pair (like the value element of a argument/value    */
/* pair) when the argument and value must be printed on separate lines.    */
/* This padding is in addition to the Pad padding.  It should be a string  */
/* of spaces.  Its length can be arbitrary, but it should probably be      */
/* a bit longer than Pad for easy reading.                                 */
/***************************************************************************/

  private static final String setOpen  = "{ ";
  private static final String setClose = " }";
  private static final String setPad   = "  ";
  private static final String setSep   = ",";
	 
  private static final String seqOpen  = "<< ";
  private static final String seqClose = " >>";
  private static final String seqPad   = "   ";
  private static final String seqSep   = ",";
	 
  private static final String funOpen   = "( ";
  private static final String funClose  = " )";
  private static final String funPad    = "  ";
  private static final String funSep    = " @@";
  private static final String funDiv    = " :>";
  private static final String funDivPad = "    ";

  private static final String recOpen   = "[ ";
  private static final String recClose  = " ]";
  private static final String recPad    = "  ";
  private static final String recSep    = ",";
  private static final String recDiv    = " |->";
  private static final String recDivPad = "    ";

  private static final String subsetOpen  = "SUBSET ";
  private static final String subsetClose = " ";
  private static final String subsetPad   = " ";
  private static final String subsetSep   = ",";
  
/***************************************************************************/
/* Format a TLC value.                                                     */
/*                                                                         */
/* Value is a parse tree for the TLC value.  Width is the number of        */
/* characters available on each line for formatting the value.             */
/* Trailerwidth is the number of characters that must not be used at the   */
/* end of the last line of the formatted value, so that trailers like      */
/* closing "}" characters can be appended and not extend past the          */
/* specified number of characters on each line.  Padding is a string       */
/* (usually spaces) tacked to the front of lines two and higher to indent  */
/* these lines in the event that the value must be formatted over          */
/* multiple lines.                                                         */
/***************************************************************************/

  public static String format(Node value, 
			      int columnwidth, 
			      int trailerwidth,
			      String leftpad) throws FormatException {

    // Use the value's original format if it will fit on the line
    if (value.length() <= columnwidth-trailerwidth) return value.value();

    // Break the value over multiple lines since it won't fit on one line
    //
    // Sets and sequences are simple lists of values enclosed by
    // delimiters.  Functions and records are more complex lists of
    // pairs of values, where each pair is a functional argument/value
    // or record field/value pair.  We use two methods to format the
    // two types of lists.

    switch (value.type()) {
    case Node.CONSTANT: 
      return value.value();
    case Node.SET: 
      return formatSimpleValue(value,columnwidth,trailerwidth,leftpad,
			       setOpen, setClose, setPad, setSep);
    case Node.SEQUENCE: 
      return formatSimpleValue(value,columnwidth,trailerwidth,leftpad,
			       seqOpen, seqClose, seqPad, seqSep);
    case Node.FUNCTION: 
      return formatPairValue(value,columnwidth,trailerwidth,leftpad,
			     funOpen, funClose, funPad, funSep, 
			     funDiv, funDivPad);
    case Node.RECORD: 
      return formatPairValue(value,columnwidth,trailerwidth,leftpad,
			     recOpen, recClose, recPad, recSep,
			     recDiv, recDivPad);
    case Node.SUBSET:
      return formatSimpleValue(value,columnwidth,trailerwidth,leftpad,
			       subsetOpen, subsetClose, subsetPad,
			       subsetSep);
    default:
      throw new FormatException("TLC Bug: while formating output," +
				" the formatter called with an expression" +
				" of type " + value.type() + 
				" while formatting " + value.value() +
				" and this should never happen");
    }
  }

/***************************************************************************/
/* Format a simple value like a set or a sequence that is a simple list    */
/* of values enclosed by delimiters.                                       */
/*                                                                         */
/* This formatting method uses a second method to format the actual list   */
/* of values, remembering to leave room for the opening and closing        */
/* delimiters when formatting this list, and then surrounds the result     */
/* with the delimiters.                                                    */
/***************************************************************************/

  private static String formatSimpleValue(Node list, 
					 int columnwidth, 
					 int trailerwidth, 
					 String leftpad,
					 String open, 
					 String close, 
					 String pad,
					 String sep) throws FormatException {
    try {
      return 
	open +
	formatValues(list.children(),
		     columnwidth-Math.max(open.length(),pad.length()),
		     trailerwidth+close.length(),
		     leftpad+pad,
		     sep) +
	close;
    }
    catch (FormatException e) {
      throw e;
    }
  }

/***************************************************************************/

  private static String formatValues(Node values, 
				    int columnwidth, 
				    int trailerwidth, 
				    String leftpad, 
				    String sep) throws FormatException {
    try {
      String pp = "";
      for (Node value = values; value != null; value = value.next()) {
	if (value.next() != null) {
	  // this is not the last value in the list, so leave room for sep
	  pp = pp + 
	    format(value,columnwidth,sep.length(),leftpad) +
	    sep + "\n" + leftpad;
	} else {
	  // this is the last value in the list
	  pp = pp +
	    format(value,columnwidth,trailerwidth,leftpad);
	}
      }
      return pp;
    }
    catch (FormatException e) {
      throw e;
    }
  }

/***************************************************************************/
/* Format a complex value like a record or a function that is a list of    */
/* pairs of values enclosed by delimiters, where each pair is a record     */
/* field/value or function argument/value pair.                            */
/*                                                                         */
/* This formatting method uses a second method to format the actual list   */
/* of values, remembering to leave room for the opening and closing        */
/* delimiters when formatting this list, and then surrounds the result     */
/* with the delimiters.                                                    */
/***************************************************************************/

  private static String formatPairValue(Node list, 
				       int columnwidth, 
				       int trailerwidth, 
				       String leftpad,
				       String open, 
				       String close, 
				       String pad,
				       String sep,
				       String div,
				       String divpad) throws FormatException {
    try {
      return 
	open +
	formatPairs(list.children(),
		    columnwidth-Math.max(open.length(),pad.length()),
		    trailerwidth+close.length(),
		    leftpad+pad,
		    sep,
		    div,
		    divpad) +
	close;
    }
    catch (FormatException e) {
      throw e;
    }
  }

/***************************************************************************/

  private static String formatPairs(Node pairs, 
				   int columnwidth,
				   int trailerwidth,
				   String leftpad,
				   String sep,
				   String div,
				   String divpad) throws FormatException {
    try {
      String pp = "";
      for (Node pair = pairs; pair != null; pair = pair.next()) {
	Node arg = pair.children();
	Node val = arg.next();

	// First suppose this pair is not the last pair in
	// the list.  In this case, don't forget to append sep to the
	// end of the value; but don't bother keeping the last
	// trailerwidth characters open at the end of the line, go
	// ahead and use them to format the value.

	if (pair.next() != null) {

	  // put argument and value on one line if they will fit
	  if (arg.length() + div.length()+ 1 + val.length() + sep.length()
	      <= columnwidth) {
	    pp = pp 
	      + arg.value() + div + " " + val.value() + sep 
              + "\n" + leftpad;
	    continue;
	  }

	  // put argument on one line if it will fit
	  if (arg.length() + div.length() <= columnwidth) {
	    pp = pp
	      + arg.value() + div 
	      + "\n" + leftpad + divpad + format(val,
						 columnwidth-divpad.length(),
						 sep.length(),
						 leftpad+divpad) + sep
	      + "\n" + leftpad;
	    continue;
	  }

	  // format the argument on multiple lines and then the value
	  pp = pp
	    + format(arg,columnwidth,trailerwidth+div.length(),leftpad) + div
	    + "\n" + leftpad + divpad + format(val,
					       columnwidth-divpad.length(),
					       sep.length(),
					       leftpad+divpad) + sep
	    + "\n" + leftpad;
	  continue;
	}

	// Now suppose this pair is the last pair in the list.
	// Remember to leave trailerwidth space at the end of the line,
	// but don't worry about appending sep to the end of the line.

	// put argument and value on one line if they will fit
	if (arg.length() + div.length() + 1 + val.length()
	    <= columnwidth-trailerwidth) {
	  pp = pp + arg.value() + div + " " + val.value();
	  continue;
	}

	// put argument alone on one line if it will fit
	if (arg.length() + div.length() <= columnwidth) {
	  pp = pp
	    + arg.value() + div 
	    + "\n" + leftpad + divpad + format(val,
					       columnwidth-divpad.length(),
					       trailerwidth,
					       leftpad+divpad);
	  continue;
	}

	// format the argument on multiple lines and then the value
	pp = pp
	  + format(arg,columnwidth,trailerwidth+div.length(),leftpad) + div
	  + "\n" + leftpad + divpad + format(val,
					     columnwidth-divpad.length(),
					     trailerwidth,
					     leftpad+divpad);
	continue;
      }
      return pp;
    }
    catch (FormatException e) {
      throw e;
    }
  }

/***************************************************************************/

}
