package tlc2.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Representation of a typed set.
 * <br>
 * This class is used for typed model values. To create an instance of this class
 * you probably want to parse it out of a string, using {@link TypedSet#parseSet(String)} method.
 * 
 * A TypedSet object appears to be used to represent a TLA+ set of the form
 * 
 *   { a1 , a2, ... , aN }
 *   
 * for N >= 0, where each ai is a TLA+ identifier.  If each of the ai begins with "C_"
 * for the same character C, then it is represented by an object having type = "C_" and
 * values[i] equal to ai with the prefix "C_" removed, for each i.  Otherwise, it is represented
 * by an object having type = null and values[i] = ai, for each i.
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TypedSet {
	public static final TypedSet EMPTY_SET = new TypedSet();
	
    private static final String SEPARATOR = "_";
    private static final String PATTERN = "[\\s]*,[\\s]*";

    
    private String[] values = new String[0];
    private String type = null;

    /**
     * Factory method
     * @param set String representation of the set
     * @return a typed set
     */
    public static TypedSet parseSet(String set)
    {
        // This code did not work properly because it could leave spaces at the
        // beginning of values[0] or end of values[value.length-1] if there
        // were spaces at the beginning or end of set or the curly braces were
        // preceded or followed by spaces. This was fixed by adding the
        // two set = set.trim(); statements and rewriting the
        // tests for an empty or null set. Changes made by LL on 11 Nov 2009.
        TypedSet result = new TypedSet();
        if (set == null)
        {
            return result;
        }
        set = set.trim();
        // if the curly braces are provided, cut them
        if (set.length() > 0 && set.charAt(0) == '{' && set.charAt(set.length() - 1) == '}')
        {
            set = set.substring(1, set.length() - 1);
            set = set.trim();
        }

        if ("".equals(set))
        {
            return result;
        }
 
        String[] parsedSet = null;

        // split by comma surrounded by any kind of spaces/tabs/new lines
        parsedSet = set.split(PATTERN);

        if (parsedSet.length > 0)
        {
            // pre-fetch first element (if no type it will store -1 there)
            int typeSeparatorPosition = parsedSet[0].indexOf("_");
            if (typeSeparatorPosition == -1 || typeSeparatorPosition == 0)
            {
                // no type, provided
                result.setValues(parsedSet);
                return result;
            } else
            {
                // type is provided
                result.setType(parsedSet[0].substring(0, typeSeparatorPosition));
                parsedSet[0] = parsedSet[0].substring(typeSeparatorPosition + 1);

                // assume that all strings have same structure
                // and set type violated to false
                // this also checks that strings like e.G. "P_", "x_" are not valid
                // because they miss the untyped part
                boolean typePatternViolated = parsedSet[0].length() == 0;

                // run through the strings and compare the position of the first "_"
                // if it changes the type patter is violated: e.G. "p_1" "pi_2".
                // also compare for the type: e.G. "p_1" "i_2"
                for (int i = 1; i < parsedSet.length; i++)
                {
                    if (parsedSet[i].startsWith(result.getType() + "_"))
                    {
                        parsedSet[i] = parsedSet[i].substring(typeSeparatorPosition + 1);
                        if (parsedSet[i].length() == 0)
                        {
                            typePatternViolated = true;
                        }
                    } else
                    {
                        typePatternViolated = true;
                    }
                    // exit if type pattern is violated
                    if (typePatternViolated)
                    {
                        break;
                    }
                }

                if (typePatternViolated)
                {
                    // violated type, restore the split
                    result.setValues(set.split(PATTERN));
                    result.setType(null);
                } else
                {
                    // type recognized
                    result.setValues(parsedSet);
                }
            }

        } else
        {
            // no values in the set...
        }

        return result;
    }

    public boolean hasType()
    {
        return (type != null);
    }

    public String getType()
    {
        return type;
    }

    // If id is a "typed" identifier, then it returns
    // the (one-character) type as a string. Else, it
    // returns null. Note that getTypeOfId("1_xyz") = "1",
    // and getTypteOfId("__z") = "z".
    public static String getTypeOfId(String id)
    {
        if (id == null || id.length() < 2 || !id.substring(1, 2).equals("_"))
        {
            return null;
        }
        return id.substring(0, 1);
    }

    public void setType(String type)
    {
        this.type = type;
    }
    
    public void unsetType() {
    	setType(null);
    }
    
    /**
     * Not remotely efficient.
     * 
     * @param value
     * @return true if the parameter value is one of this set's values.
     */
    public boolean contains(final String value) {
    	if (value != null) {
    		for (final String aValue : values) {
    			if (value.equals(aValue)) {
    				return true;
    			}
    		}
    	}
    	
    	return false;
    }

    public String[] getValues()
    {
        return values;
    }

    /**
     * Convenience interface for iteration over the values
     * This method disconnects the actual typed set from the collection of values
     * @return a list containing the values
     */
    public List<String> getValuesAsList()
    {
        if (!hasType())
        {
            return Arrays.asList(values);
        } else
        {
            List<String> typedList = new ArrayList<String>(values.length);
            // add type to the list
            for (int i = 0; i < values.length; i++)
            {
                String value = type + SEPARATOR + values[i];
                typedList.add(value);
            }
            return typedList;
        }
    }

    /**
     * retrieves the number of values in the set
     * @return number of values in the set, or null if none
     */
    public int getValueCount()
    {
        if (values == null)
        {
            return 0;
        } else
        {
            return values.length;
        }
    }

    /**
     * Retrieves a value by index
     * @param index, index of the value, should be smaller then the value of {@link TypedSet#getValueCount()}
     * @return value (with type, if any) or null if index out of range 
     */
    public String getValue(int index)
    {
        if (index >= getValueCount())
        {
            return null;
        } else
        {
            return (hasType() ? getType() + SEPARATOR : "") + values[index];
        }
    }

    public void setValues(String[] values)
    {
        if (values == null)
        {
            this.values = new String[0];
        } else
        {
            this.values = values;
        }
    }

    public int hashCode()
    {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((type == null) ? 0 : type.hashCode());
        result = prime * result + TypedSet.hashCode(values);
        return result;
    }

    private static int hashCode(Object[] array)
    {
        int prime = 31;
        if (array == null)
            return 0;
        int result = 1;
        for (int index = 0; index < array.length; index++)
        {
            result = prime * result + (array[index] == null ? 0 : array[index].hashCode());
        }
        return result;
    }

    /**
     * Two typed sets are equals if they have
     * the same type and the elements of the set are the same
     * (and appear in the same order)
     */
    public boolean equals(Object obj)
    {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        TypedSet other = (TypedSet) obj;
        if (type == null)
        {
            if (other.type != null)
                return false;
        } else if (!type.equals(other.type))
            return false;
        if (!Arrays.equals(values, other.values))
            return false;
        return true;
    }

    /**
     * The string implementation of the typed set
     * Is used to be set in the right side of assignment ({@link Assignment#setRight(String)})
     * <br><b>Note:</b> {@link TypedSet#toString()} should not be used for comparison
     * @see TypedSet#equals(Object)
     */
    public String toString()
    {
        StringBuffer buffer = new StringBuffer("{");
        for (int i = 0; i < this.values.length; i++)
        {
            if (this.type != null)
            {
                buffer.append(this.type).append(SEPARATOR);
            }
            buffer.append(this.values[i]);
            if (i != this.values.length - 1)
            {
                buffer.append(", ");
            }
        }
        buffer.append("}");
        return buffer.toString();
    }

    /**
     * Same as toString, but without curly braces
     * @return
     */
    public String toStringWithoutBraces()
    {
        String set = toString();
        return set.substring(1, set.length() - 1);
    }

    /**
     * This test functions checks whether the type has at least one value
     * that contain only of digits
     * @return true if on of the values (taking the type into account) is a digit
     * @deprecated
     */
    public boolean hasANumberOnlyValue()
    {
        if (hasType())
        {
            return !hasValidType();
        } else
        {
            for (int i = 0; i < values.length; i++)
            {
                if (values[i].matches("[0-9]*"))
                {
                    // a digit sequence found
                    return true;
                }
            }
            return false;
        }
    }

    public boolean hasValidType()
    {
        if (type != null)
        {
            if (!type.matches("[A-Za-z]{1}[A-Za-z0-9]*"))
            {
                // the type must be a valid identifier
                return false;
            }
        }
        return true;
    }
}
