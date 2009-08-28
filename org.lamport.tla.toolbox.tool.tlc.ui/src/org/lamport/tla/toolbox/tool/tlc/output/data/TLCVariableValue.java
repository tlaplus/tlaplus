package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.Assert;

/**
 * A representation of a variable value
 * @author Simon Zambrovski
 * @version $Id$
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

        StringBuffer buffer = new StringBuffer(delimeters[0]);
        if (elements.length == 0)
        {
            buffer.append(SPACE);
        } else
        {
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

        StringBuffer buffer = new StringBuffer(delimeters[0]);
        if (elements.length == 0)
        {
            buffer.append(SPACE);
        } else
        {
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

            List sequenceValues = new Vector();
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
            List recordPairs = new Vector();

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
            List fcnElements = new Vector();

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
            List setValues = new Vector();
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
