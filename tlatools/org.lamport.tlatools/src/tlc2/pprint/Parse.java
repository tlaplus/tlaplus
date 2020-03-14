// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:21:03 PST by lamport
//      modified on Wed Jun 16 14:39:09 EDT 1999 by tuttle
//      modified on Fri Jun 11 17:52:19 PDT 1999 by yuanyu

package tlc2.pprint;

public class Parse {

/* *********************************************************************** */
/* This class provides a parse method that accepts a string                */
/* representation of a TLC value and an integer indexing into that         */
/* string, and the method returns a parse tree for the subvalue starting   */
/* at the designated index in the string.                                  */
/* *********************************************************************** */

/* *********************************************************************** */
/* The following constants aid in parsing the string representation of     */
/* TLC values.                                                             */
/*                                                                         */
/* Open and Close give the initial character of the strings like "{" and   */
/* "}" used as the opening and closing delimters for a value like a set.   */
/*                                                                         */
/* Sep gives the string that should follow the component of a value to     */
/* separate it from the next component, like "," between elements of a     */
/* set or "@@" between pairs of values defining the function.              */
/*                                                                         */
/* Div gives the string like "|->" separating elements of pairs like the   */
/* name/value pairs defining a field in a record or like ":>" separating   */
/* the argument/value pairs defining a function.                           */
/* *********************************************************************** */

  private static final char setOpen = '{';
  private static final char setClose = '}';

  private static final char seqOpen = '<';
  private static final char seqClose = '>';

  private static final char recOpen = '[';
  private static final char recClose = ']';
  private static final String recDiv = "|->";
  // SZ Jul 13, 2009: not used:
  // private static final String recSep = ",";

  private static final char funOpen = '(';
  private static final char funClose = ')';
  private static final String funDiv = ":>";
  private static final String funSep = "@@";

  private static final String intDiv = "..";
  private static final String ssDiv = "SUBSET";  

/***************************************************************************/
/* Parse a TLC value.                                                      */
/*                                                                         */
/* String is a representation of a TLC value as produced by the toString   */
/* method, and index is an index pointing to a subvalue of the value       */
/* given by string.                                                        */
/***************************************************************************/

  static public Node parse(String string, int index) throws ParseException {

    if (string == null) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter was called with a null" +
			       " string for a value");
    }
    if (string.length() == 0) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter was called with an empty" +
			       " string for a value");
    }
    if (index < 0 || index > string.length() - 1) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter was called with a string " + 
			       string + " for a value and an index " + index + 
			       " out of bounds");
    }

    try {
      index = skipWhitespace(string,index);

      if (string.charAt(index) == setOpen) {
	return parseSet(string,index);
      }
      if (string.charAt(index) == seqOpen) {
	return parseSequence(string,index);
      }
      if (string.charAt(index) == recOpen) {
	return parseRecord(string,index);
      }
      if (string.charAt(index) == funOpen) {
	return parseFunction(string,index);
      }
      if (string.regionMatches(index, ssDiv, 0, ssDiv.length())) {
	return parseSubset(string, index);
      }
      return parseConstant(string,index);
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/
/* Parse a set.                                                            */
/*                                                                         */
/* Assume that index points to the setOpen character '{' in string.        */
/***************************************************************************/

  private static Node parseSet(String string, int index) 
    throws ParseException {

    int first = index;
    int last = index;

    try {
      // construct the parse tree node for this set
      Node node = new Node(string,first,Node.SET);

      // initialize the list of parse tree nodes for the elements of this set
      Node firstelement = null;
      Node lastelement = null;

      // skip the '{' character and following whitespace
      last++;
      last = skipWhitespace(string,last);

      // parse comma-separated elements in set up to a '}' character
      while (string.charAt(last) != setClose) {

	// construct parse tree node for this element
	Node elt = parse(string,last);

	// append node for this element to list of set elements
	if (firstelement == null) {
	  firstelement = elt;
	  lastelement = elt;
	} else {
	  lastelement.next(elt);
	  lastelement = elt;
	}

	// point to character after this element
	last = elt.last() + 1;

	// skip the comma between elements, and surrounding whitespace
	last = skipWhitespace(string,last);
	if (string.charAt(last) == ',') last++;
	last = skipWhitespace(string,last);

      }
      node.children(firstelement);
      node.last(last);
      
      return node;
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the" +
			       " string while parsing a set starting at" +
			       " index " + index + " in the value " + 
			       string + "\n" +
			       e.getMessage());
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/
/* Parse a set.                                                            */
/*                                                                         */
/* Assume that index points to the seqOpen character '<' in string.        */
/***************************************************************************/

  private static Node parseSequence(String string, int index) 
    throws ParseException {

    int first = index;
    int last = index;

    try {
      // construct the parse tree node for this sequence
      Node node = new Node(string,first,Node.SEQUENCE);

      // initialize the list of parse tree nodes for the elements of sequence
      Node firstelement = null;
      Node lastelement = null;

      // skip the '<<' token and following whitespace
      last++; last++;
      last = skipWhitespace(string,last);

      // parse comma-separated elements in sequence up to a '>>' token
      while (string.charAt(last) != seqClose) {

	// construct parse tree node for this element
	Node elt = parse(string,last);

	// append node for this element to list of sequence elements
	if (firstelement == null) {
	  firstelement = elt;
	  lastelement = elt;
	} else {
	  lastelement.next(elt);
	  lastelement = elt;
	}

	// point to character after this element
	last = elt.last() + 1;

	// skip the comma between elements, and surrounding whitespace
	last = skipWhitespace(string,last);
	if (string.charAt(last) == ',') last++;
	last = skipWhitespace(string,last);

      }
      // point to the second '>' in the '>>' token
      last++;

      node.children(firstelement);
      node.last(last);
      
      return node;
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the string" +
			       " while parsing a sequence starting at index " +
			       index + " in the value " + string + "\n" +
			       e.getMessage());
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/
/* Parse a record.                                                         */
/*                                                                         */
/* Assume that index points to the recOpen character '[' in string.        */
/* A record is a sequence of comma-separated pairs of the form             */
/* "name|->value".  This method uses an auxiliary method to parse these    */
/* pairs.                                                                  */
/***************************************************************************/

  private static Node parseRecord(String string, int index) 
    throws ParseException {

    int first = index;
    int last = index;

    try {
      // construct the parse tree node for this record
      Node node = new Node(string,first,Node.RECORD);

      // initialize the list of parse tree nodes for the pairs of this record
      Node firstelement = null;
      Node lastelement = null;

      // skip the '[' character and following whitespace
      last++;
      last = skipWhitespace(string,last);

      // parse comma-separated pairs in record up to a ']' character
      while (string.charAt(last) != recClose) {

	// construct parse tree node for this element
	Node elt = parseRecordPair(string,last);

	// append node for this element to list of record elements
	if (firstelement == null) {
	  firstelement = elt;
	  lastelement = elt;
	} else {
	  lastelement.next(elt);
	  lastelement = elt;
	}

	// point to character after this element
	last = elt.last() + 1;

	// skip the comma between elements, and surrounding whitespace
	last = skipWhitespace(string,last);
	if (string.charAt(last) == ',') last++;
	last = skipWhitespace(string,last);

      }
      node.children(firstelement);
      node.last(last);
      
      return node;
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the string" +
			       " while parsing a record starting at index " +
			       index + " in the value " + string + "\n" +
			       e.getMessage());
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/

  private static Node parseRecordPair(String string, int index) 
    throws ParseException {
    // Assume that index points to the start of a "field|->value" 
    // record pair in string

    int first = index;
    int last = index;

    try {
      // construct the parse tree node for this record
      Node node = new Node(string,first,Node.RECORDPAIR);
      Node field = null;
      Node value = null;

      // get field name
      field = parse(string,last);

      // point to position just past field name in string
      last = field.last()+1;

      // skip the '|->' token and the surrounding whitespace
      last = skipWhitespace(string,last);
      if (!string.regionMatches(last,recDiv,0,recDiv.length())){
	throw new ParseException("TLC Bug: while formating output," +
				 " the formatter couldn't find" +
				 " the token " + recDiv +
				 " while parsing a record field/value pair" +
				 " starting at index " + index +
				 " in value " + string);
      }
      last = last + recDiv.length();
      last = skipWhitespace(string,last);      

      // get field value
      value = parse(string,last);

      // make field name and value children of the record pair node
      field.next(value);
      node.children(field);
      node.last(value.last());
      
      return node;
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the string" +
			       " while parsing a record pair starting" +
			       " at index " + index + 
			       " in the value " + string + "\n" 
			       + e.getMessage());
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/
/* Parse a function.                                                       */
/*                                                                         */
/* Assume that index points to the funOpen character '(' in string.  A     */
/* record is a sequence of @@-separated pairs of the form "arg|->value".   */
/* This method uses an auxiliary method to parse these pairs.              */
/***************************************************************************/

  private static Node parseFunction(String string, int index) 
    throws ParseException {

    int first = index;
    int last = index;

    try {
      // construct the parse tree node for this function
      Node node = new Node(string,first,Node.FUNCTION);

      // initialize the list of parse tree nodes for the pairs of this function
      Node firstpair = null;
      Node lastpair = null;

      // skip the '(' character and following whitespace
      last++;
      last = skipWhitespace(string,last);

      // parse the pairs in function up to a ')' character
      while (string.charAt(last) != funClose) {

	// construct parse tree node for this pair
	Node pair = parseFunctionPair(string,last);

	// append node for this pair to list of function pairs
	if (firstpair == null) {
	  firstpair = pair;
	  lastpair = pair;
	} else {
	  lastpair.next(pair);
	  lastpair = pair;
	}

	// point to character after this pair
	last = pair.last() + 1;

	// skip the separator between pairs, and surrounding whitespace
	last = skipWhitespace(string,last);
	if (string.regionMatches(last,funSep,0,
				  funSep.length())){
	  last = last + funSep.length();
	}
	last = skipWhitespace(string,last);      
      }
      node.children(firstpair);
      node.last(last);
      
      return node;
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the string" +
			       " while parsing a function starting" +
			       " at index " + index + 
			       " in the value " + string + "\n" +
			       e.getMessage());
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/
/* Parse a SUBSET.                                                         */
/*                                                                         */
/* Assume that index points to the start of the substring "SUBSET".        */
/***************************************************************************/
  private static Node parseSubset(String string, int index)
    throws ParseException {
    int first = index;
    int last = index;

    try {
      Node node = new Node(string, first, Node.SUBSET);

      // skip the 'SUBSET' and following whitespace
      last += 6;
      last = skipWhitespace(string, last);

      Node elt = parse(string, last);
      node.children(elt);
      node.last(elt.last());

      return node;
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the" +
			       " string while parsing a SUBSET starting" +
			       " at index " + index + " in the value " + 
			       string + "\n" + e.getMessage());
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/

  private static Node parseFunctionPair(String string, int index) 
    throws ParseException {
    // Assume that index points to the start of a "domain:>range" pair 
    // in the string defining a function.

    int first = index;
    int last = index;

    try {
      // construct the parse tree node for this function
      Node node = new Node(string,first,Node.FUNCTIONPAIR);
      Node domain = null;
      Node range = null;

      // get domain value
      domain = parse(string,last);

      // point to position just past domain value in string
      last = domain.last()+1;

      // skip the '|->' token and the surrounding whitespace
      last = skipWhitespace(string,last);
      if (!string.regionMatches(last,funDiv,0,funDiv.length())){
	throw new ParseException("TLC Bug: while formating output," +
				 " the formatter couldn't find token " 
				 + funDiv
				 + " while parsing a function arg/value pair"
				 + " starting at index " + index 
				 + " in value " + string);
      }
      last = last + funDiv.length();
      last = skipWhitespace(string,last);      

      // get range value
      range = parse(string,last);

      // make domain and range values children of the function pair node
      domain.next(range);
      node.children(domain);
      node.last(range.last());
      
      return node;
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the string"+
			       " while parsing a function pair starting at" +
			       " index " + index + " in the value " + 
			       string + "\n" + e.getMessage());
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/
/* Parse a constant.                                                       */
/*                                                                         */
/* The only constants are strings, booleans, integers, and model values.   */
/***************************************************************************/

  private static Node parseConstant(String string, int index) 
    throws ParseException {
    
    try {
      int first = skipWhitespace(string,index);
      int last = first;
    
      if (string.charAt(first) == '"') {
	// we are parsing a string constant
	do
	  last++;
	while (string.charAt(last) != '"');
	return new Node(string,first,last,Node.CONSTANT);
      }

      if (Character.isDigit(string.charAt(last))) {
	// we might be parsing an constant inteval i..j
	Node node = parseInterval(string,index);
	if (node != null) return node;
      }

      if (string.charAt(last) == '-') {
	// we are parsing a negative integer
	last++;
	while (Character.isDigit(string.charAt(last))) {
	  last++;
	  if (last == string.length()) break;
	}
	last--;
	return new Node(string,first,last,Node.CONSTANT);
      }
      
      if (Character.isLetterOrDigit(string.charAt(last))) {
	// we are parsing an integer, boolean, or model value
	while (Character.isLetterOrDigit(string.charAt(last))) {
	  last++;
	  if (last == string.length()) break;
	}
	last--;
	return new Node(string,first,last,Node.CONSTANT);
      }

      // we have encountered an illegal character in a constant
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter discovered an illegal" +
			       " character while parsing a constant" +
			       " starting at index " + first + 
			       " in the value " + string);
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the string" +
			       " while parsing a constant starting at index " +
			       index + " in the value " + string + "\n" +
			       e.getMessage());
    }
    catch (ParseException e) {
      throw e;
    }
  }

/***************************************************************************/
/* Parse a constant interval of the form i..j for integers i and j.        */
/*                                                                         */
/* Assume that index is pointing to an integer in string.  Return a null   */
/* pointer if the parsing fails, rather that throwing an exception as      */
/* other parsing routines do.                                              */
/***************************************************************************/

  private static Node parseInterval(String string, int index) {
    
    try {
      int first = index;
      int last = first;
    
      // parse the first integer i
      if (! Character.isDigit(string.charAt(last)) ) return null;
      while (Character.isDigit(string.charAt(last))) {
	last++;
      }

      // parse the interval constructor ".."
      if (! string.startsWith(intDiv,last) ) return null;
      last++; last++;

      // parse the second integer j
      if (! Character.isDigit(string.charAt(last)) ) return null;
      while (Character.isDigit(string.charAt(last))) {
	last++;
	if (last == string.length()) break;
      }
      last--;
					       
      return new Node(string,first,last,Node.CONSTANT);
    }
    catch (StringIndexOutOfBoundsException e) {
      // bail if we run off the string during parsing
      return null;
    }
  }


/***************************************************************************/
/* Skip whitespace starting at index in string, and return the index of    */
/* the first non-whitespace character, throwing an exception if we run     */
/* off the end of the string.                                              */
/***************************************************************************/

  public static int skipWhitespace(String string, int index) 
    throws ParseException{

    try {
      int i = index;
      while (Character.isWhitespace(string.charAt(i))) {
	i++;    
      }
      return i;
    }
    catch (StringIndexOutOfBoundsException e) {
      throw new ParseException("TLC Bug: while formating output," +
			       " the formatter ran off the end of the string" +
			       " while skipping whitespace starting" +
			       " at index " + index + 
			       " in the value " + string + "\n" +
			       e.getMessage());
    }
  }

/***************************************************************************/

}
