/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.Assert;

/**
 * A representation of a variable value
 * @author Simon Zambrovski
 */
public abstract class TLCVariableValue
{

    /**
     * Factory method to deliver simple values
     * @param input
     * @return
     */
    public static TLCVariableValue parseValue(String input)
    {
        Assert.isNotNull(input, "The value must be not null");
        input.trim();

        TLCVariableValue result;

        try
        {
            InputPair pair = new InputPair(input, 0);
            result = innerParse(pair);
            if (pair.offset != input.length())
            {
                throw new VariableValueParseException();
            }
        } catch (VariableValueParseException e)
        {
            result = new TLCSimpleVariableValue(input);
        }

        return result;
    }

    private static final char CBRACKET = ']';
    private static final char OBRACKET = '[';
    private static final char OPAREN = '(';
    private static final char CPAREN = ')';
    private static final char LT = '<';
    private static final char GT = '>';
    private static final char OCBRACE = '{';
    private static final char CCBRACE = '}';
    private static final char QUOTE = '"';
    private static final char ESC = '\\';
    private static final char COMMA = ',';
    private static final char ATSIGN = '@';
    private static final char COLON = ':';
    private static final char PIPE = '|';
    private static final char MINUS = '-';

    private static final char CR = '\n';
    private static final char SPACE = ' ';

    private static final Pattern ATOMIC_PATERN = Pattern.compile("[-.0-9a-zA-Z_]*");

    /**
     * Format the array for pretty printing
     * @param elements
     * @param delimeters three strings, opening, element separator, closing 
     * @return
     */
    public static StringBuffer arrayToStringBuffer(Object[] elements, String[] delimeters)
    {
        Assert.isNotNull(delimeters);

        StringBuffer buffer;
        if (elements.length == 0)
        {
        	buffer = new StringBuffer(3);
            buffer.append(delimeters[0]);
            buffer.append(SPACE);
        } else
        {
        	buffer = new StringBuffer((elements.length * 3) + 2);
        	buffer.append(delimeters[0]);
            for (int i = 0; i < elements.length; i++)
            {
                buffer.append(elements[i].toString());
                if (i != elements.length - 1)
                {
                    buffer.append(delimeters[1]);
                    buffer.append(SPACE);
                }
            }
        }
        buffer.append(delimeters[2]);
        return buffer;
    }

    public static StringBuffer arrayToSimpleStringBuffer(Object[] elements, String[] delimeters)
    {
        Assert.isNotNull(delimeters);

        StringBuffer buffer = null;
        if (elements.length == 0)
        {
        	buffer = new StringBuffer(3);
            buffer.append(delimeters[0]);
            buffer.append(SPACE);
        } else
        {
        	buffer = new StringBuffer((elements.length * 3) + 2);
            buffer.append(delimeters[0]);
            for (int i = 0; i < elements.length; i++)
            {
                if (elements[i] instanceof TLCVariableValue)
                {
                    buffer.append(((TLCVariableValue) elements[i]).toSimpleString());
                } else
                {
                    buffer.append(elements[i].toString());
                }

                if (i != elements.length - 1)
                {
                    buffer.append(delimeters[1]);
                    buffer.append(SPACE);
                }
            }
        }
        buffer.append(delimeters[2]);
        return buffer;
    }

    /**
     * Parses the string into a typed variable value
     * @param input
     * @param offset
     * @return
     * @throws VariableValueParseException
     */
    static TLCVariableValue innerParse(InputPair input) throws VariableValueParseException
    {

        TLCVariableValue result = null;
        TLCVariableValue innerValue;
        int initialOffset = input.offset;

        char ch = getNextChar(input);
        char nextCh;

        switch (ch) {
        // sequence
        case LT:
            nextCh = getNextChar(input);
            if (nextCh != LT)
            {
                throw new VariableValueParseException();
            }

            List<TLCVariableValue> sequenceValues = new Vector<TLCVariableValue>();
            innerValue = innerParse(input);
            if (innerValue != null)
            {
                sequenceValues.add(innerValue);
                nextCh = getNextChar(input);
                while (nextCh == COMMA)
                {
                    sequenceValues.add(innerParse(input));
                    nextCh = getNextChar(input);
                }
                if (nextCh != GT || getNextChar(input) != GT)
                {
                    throw new VariableValueParseException();
                }
            }
            result = new TLCSequenceVariableValue(sequenceValues);
            break;

        // empty sequence
        case GT:
            nextCh = getNextChar(input);
            if (nextCh != GT)
            {
                throw new VariableValueParseException();
            }
            return null;

        case OBRACKET:
            List<TLCVariableValue> recordPairs = new Vector<TLCVariableValue>();

            TLCVariableValue innerValue2;

            // fetch the first one
            innerValue = innerParse(input);
            if (innerValue != null)
            {
                if (!(innerValue instanceof TLCSimpleVariableValue))
                {
                    // left side should be a simple value (String)
                    throw new VariableValueParseException();
                }

                if (getNextChar(input) == PIPE && getNextChar(input) == MINUS && getNextChar(input) == GT)
                {
                    innerValue2 = innerParse(input);
                    if (innerValue2 == null)
                    {
                        // no right side of |->
                        throw new VariableValueParseException();
                    }

                    recordPairs.add(new TLCNamedVariableValue((String) innerValue.value, innerValue2));
                } else
                {
                    // no |->
                    throw new VariableValueParseException();
                }
            }

            nextCh = getNextChar(input);
            while (nextCh == COMMA)
            {
                innerValue = innerParse(input);
                if (innerValue != null)
                {
                    if (!(innerValue instanceof TLCSimpleVariableValue))
                    {
                        // left side should be a simple value (String)
                        throw new VariableValueParseException();
                    }

                    if (getNextChar(input) == PIPE && getNextChar(input) == MINUS && getNextChar(input) == GT)
                    {
                        innerValue2 = innerParse(input);
                        if (innerValue2 == null)
                        {
                            // no right side of |->
                            throw new VariableValueParseException();
                        }

                        recordPairs.add(new TLCNamedVariableValue((String) innerValue.value, innerValue2));
                    } else
                    {
                        // no |->
                        throw new VariableValueParseException();
                    }
                }

                nextCh = getNextChar(input);
            }
            if (nextCh != CBRACKET)
            {
                throw new VariableValueParseException();
            }

            result = new TLCRecordVariableValue(recordPairs);
            break;
        case CBRACKET:
            return null;
        case OPAREN:
            List<TLCVariableValue> fcnElements = new Vector<TLCVariableValue>();

            TLCVariableValue domElement;

            // fetch the first one
            domElement = innerParse(input);
            if (domElement != null)
            {
                if (getNextChar(input) == COLON && getNextChar(input) == GT)
                {
                    innerValue = innerParse(input);
                    if (innerValue == null)
                    {
                        // no right side of |->
                        throw new VariableValueParseException();
                    }

                    fcnElements.add(new TLCFcnElementVariableValue(domElement, innerValue));
                } else
                {
                    // no :>
                    throw new VariableValueParseException();
                }
            }

            nextCh = getNextChar(input);
            while (nextCh == ATSIGN)
            {
                if (getNextChar(input) != ATSIGN)
                {
                    // no second @
                    throw new VariableValueParseException();
                }
                domElement = innerParse(input);
                if (domElement != null)
                {
                    if (getNextChar(input) == COLON && getNextChar(input) == GT)
                    {
                        innerValue = innerParse(input);
                        if (innerValue == null)
                        {
                            // no right side of |->
                            throw new VariableValueParseException();
                        }

                        fcnElements.add(new TLCFcnElementVariableValue(domElement, innerValue));
                    } else
                    {
                        // no |->
                        throw new VariableValueParseException();
                    }
                }

                nextCh = getNextChar(input);
            }
            if (nextCh != CPAREN)
            {
                throw new VariableValueParseException();
            }

            result = new TLCFunctionVariableValue(fcnElements);
            break;

        case CPAREN:
            throw new VariableValueParseException();

        case OCBRACE:
            List<TLCVariableValue> setValues = new Vector<TLCVariableValue>();
            innerValue = innerParse(input);
            if (innerValue != null)
            {
                setValues.add(innerValue);
                nextCh = getNextChar(input);
                while (nextCh == COMMA)
                {
                    setValues.add(innerParse(input));
                    nextCh = getNextChar(input);
                }
                if (nextCh != CCBRACE)
                {
                    throw new VariableValueParseException();
                }
            }

            result = new TLCSetVariableValue(setValues);
            break;
        // empty set
        case CCBRACE:
            return null;

        default:
            if (ch != QUOTE)
            {
                Matcher matcher = ATOMIC_PATERN.matcher(input.input.substring(input.offset - 1));
                if (matcher.find())
                {
                    if (matcher.start() == 0)
                    {
                        result = new TLCSimpleVariableValue(input.input.substring(input.offset - 1, input.offset
                                + matcher.end() - 1));

                        input.offset = input.offset + matcher.end() - 1;
                        // break ;
                        return result;
                    }
                }

                throw new VariableValueParseException();
            } else
            { /* ch equals QUOTE */
                int startOfString = input.offset - 1;
                if (input.offset >= input.input.length())
                {
                    throw new VariableValueParseException();
                }
                ;
                while (input.input.charAt(input.offset) != QUOTE)
                {
                    if (input.input.charAt(input.offset) == ESC)
                    {
                        input.offset++;
                    }
                    input.offset++;
                    if (input.offset >= input.input.length())
                    {
                        throw new VariableValueParseException();
                    }
                    ;
                }
                input.offset++;
                return new TLCSimpleVariableValue(input.input.substring(startOfString, input.offset));
            }
        }
        result.source = input.input.substring(initialOffset, input.offset).trim();
        return result;
    }

    /**
     * Retrieves the next character jumping spaces and new lines 
     * @param input
     * @return
     * @throws VariableValueParseException
     */
    static char getNextChar(InputPair input) throws VariableValueParseException
    {
        if (input.offset < 0 || input.offset >= input.input.length())
        {
            throw new VariableValueParseException();
        } else
        {
            char ch = input.input.charAt(input.offset++);
            // skipping spaces and new lines
            if (ch == SPACE || ch == CR)
            {
                return getNextChar(input);
            }
            return ch;
        }
    }

    protected Object value;

    /* The input string that produced this value, except it is null for 
     * parts of a value--that is, for TLCFcnElementVariableValue and 
     * TLCNamedVariableValue objects--and for TLCSimpleVariableValue 
     * objects. */
    protected String source = null;
    
    private short diffState = 0;

    public Object getValue()
    {
        return value;
    }

    /* 
     * For objects that represent a value, the toString method returns 
     * the value as printed by TLC's pretty-printer.
     */
    public String toString()
    {
        return source; // value.toString();
    }

    /*
     * The toSimpleString() method returns a single-line string
     * representation of the object.  The following method should
     * be overridden for complex values.
     */
    public String toSimpleString()
    {
        return value.toString();
    }

    public int getChildCount() {
    	if (this.value instanceof List) {
    		return ((List) this.value).size();
    	} else if (this.value instanceof TLCVariableValue) {
    		return ((TLCVariableValue) this.value).getChildCount();
    	}
    	return 0;
    }

    /*
     * Here are the three states that contain the objects
     * representing rows in the table displaying the trace that should be
     * highlighted. They have the following meanings:
     * 
     * changed: Rows indicating values that have changed from the last
     * state. Subobjects of the value column of such a row could also be
     * highlighted.
     * 
     * added: Rows that have been added to a value since the last state.
     * 
     * deleted: Rows that are deleted in the following state.
     * 
     * The same row can appear in both the deleted and the
     * changed or added. In that case, it should be displayed as
     * a changed or added row--since we can't do multicolored backgrounds to
     * show that it is both.
     */
    protected void setDeleted() {
		 diffState |= (1 << 2);
	}

	/**
	 * @return true iff this value has been delete compared to the predecessor
	 *         state's value in the error trace.
	 */
	public boolean isDeleted() {
		return ((diffState>>2) & 1) != 0;
	}
	
	protected void setAdded() {
		 diffState |= (1 << 1);
	}

	/**
	 * @return true iff this value has been added compared to the predecessor
	 *         state's value in the error trace.
	 */
	public boolean isAdded() {
		return ((diffState>>1) & 1) != 0;
	}
	
	protected void setChanged() {
		 diffState |= (1 << 0);
	}

	/**
	 * @return true iff this value is different to the predecessor state's value
	 *         in the error trace.
	 */
	public boolean isChanged() {
		return ((diffState>>0) & 1) != 0;
	}

	/**
	 * The recursive method called by innerDiff that diffs the subobjects of
	 * the variable value objects to indicate which rows of
	 * the hierarchical trace table should be highlighted to show the parts of
	 * the state that have changed.
	 */
	public void diff(TLCVariableValue other) {
		if (!this.toSimpleString().equals(other.toSimpleString())) {
			other.setChanged();
			if (this.getClass().equals(other.getClass())) {
				// Only diff objects of identical types
				innerDiff(other);
			}
		}
	}

	protected void innerDiff(TLCVariableValue other) {
		// nothing to be done generally, subclass may override
		return;
	}

	/**
	 * A method that sets the diff highlighting information for two arrays of
	 * either TLCFcnElementVariableValue or TLCNamedVariableValue objects,
	 * representing the value elements of twos values represented by
	 * TLCFunctionVariableValue, TLCRecordVariableValue, or
	 * TLCSequenceVariableValue objects. The parameters firstElts and secondElts
	 * are the two arrays, and firstLHStrings and secondLHStrings are the
	 * results of applying the toString or toSimpleString method to their first
	 * elements. In plain math, this means that we are doing a diff on two
	 * functions (possibly two records or two sequences) where the ...Strings
	 * arrays are string representations of the domain elements of each of the
	 * function elements.
	 * 
	 * The HashSet arguments are the sets of element objects that are to be
	 * highlighted in the appropriate fashion.
	 * 
	 * We mark a function element as added or deleted if its left-hand value
	 * does not appear in one of the elements of the other function. We mark the
	 * element as changed, and call setInnerDiffInfo on the elements' values if
	 * elements with the same left-hand values having different values appear in
	 * the two records.
	 */
	protected void setElementArrayDiffInfo(TLCVariableValue[] firstElts, String[] firstLHStrings,
			TLCVariableValue[] secondElts, String[] secondLHStrings) {

		for (int i = 0; i < firstElts.length; i++) {
			boolean notfound = true;
			int j = 0;
			while (notfound && j < secondElts.length) {
				if (firstLHStrings[i].equals(secondLHStrings[j])) {
					notfound = false;
					TLCVariableValue first = (TLCVariableValue) firstElts[i].getValue();
					TLCVariableValue second = (TLCVariableValue) secondElts[j].getValue();
					if (!first.toSimpleString().equals(second.toSimpleString())) {
						second.setChanged();
						if (first.getClass().equals(second.getClass())) {
							// Only diff objects of identical types
							first.innerDiff(second);
						}
					}
				}
				j++;
			}
			if (notfound) {
				firstElts[i].setDeleted();
			}
		}

		for (int i = 0; i < secondElts.length; i++) {
			boolean notfound = true;
			int j = 0;
			while (notfound && j < firstElts.length) {
				if (firstElts[j].toSimpleString().equals(secondElts[i].toSimpleString())) {
					notfound = false;
				}
				j++;
			}
			if (notfound) {
				secondElts[i].setAdded();
			}
		}
	}

	/**
	 * A method that sets the diff highlighting information for two arrays of
	 * TLCFcnElementVariableValue objects. The parameters firstElts and
	 * secondElts are the two arrays.In plain math, this means that we are doing
	 * a diff on two functions (possibly two sequences). This method calls
	 * setElementArrayDiffInfo to do the work.
	 */
	protected void setFcnElementArrayDiffInfo(TLCFcnElementVariableValue[] firstElts,
			TLCFcnElementVariableValue[] secondElts) {
		final String[] firstLHStrings = new String[firstElts.length];
		for (int i = 0; i < firstElts.length; i++) {
			firstLHStrings[i] = firstElts[i].getFrom().toSimpleString();
		}
		final String[] secondLHStrings = new String[secondElts.length];
		for (int i = 0; i < secondElts.length; i++) {
			secondLHStrings[i] = secondElts[i].getFrom().toSimpleString();
		}
		setElementArrayDiffInfo(firstElts, firstLHStrings, secondElts, secondLHStrings);
	}

    static class InputPair
    {
        String input;
        int offset;

        public InputPair(String input, int offset)
        {
            this.input = input;
            this.offset = offset;
        }

    }

    /**
     * 
     *
     */
    static class VariableValueParseException extends Throwable
    {

    }

}
