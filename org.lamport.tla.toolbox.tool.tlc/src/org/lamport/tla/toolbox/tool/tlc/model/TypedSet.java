package org.lamport.tla.toolbox.tool.tlc.model;

import java.util.Arrays;

/**
 * Representation of a typed set.
 * <br>
 * This class is used for typed model values. To create an instance of this class
 * you probably want to parse it out of a string, using {@link TypedSet#parseSet(String)} method.
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TypedSet
{
    private static final String SEPARATOR = "_";
    private static final String PATTERN = "[\\s]*,[\\s]*";

    private String[] values = null;
    private String type = null;

    /**
     * Factory method
     * @param set String representation of the set
     * @return a typed set
     */
    public static TypedSet parseSet(String set)
    {
        TypedSet result = new TypedSet();
        
        if (set == null || "".equals(set)) 
        {
            return result;
        }
        
        String[] parsedSet = null;
        // if the curly braces are provided, cut them
        if (set.charAt(0) == '{' && set.charAt(set.length() - 1) == '}')
        {
            set = set.substring(1, set.length() - 1);
        }
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
                boolean typePatternViolated = parsedSet[0].isEmpty();

                // run through the strings and compare the position of the first "_"
                // if it changes the type patter is violated: e.G. "p_1" "pi_2".
                // also compare for the type: e.G. "p_1" "i_2"
                for (int i = 1; i < parsedSet.length; i++)
                {
                    if (parsedSet[i].startsWith(result.getType() + "_"))
                    {
                        parsedSet[i] = parsedSet[i].substring(typeSeparatorPosition + 1);
                        if (parsedSet[i].isEmpty()) 
                        {
                            typePatternViolated = true;
                        }
                    } else
                    {
                        typePatternViolated = true;
                    }
                    // exit if type pattern is vialated
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

    public void setType(String type)
    {
        this.type = type;
    }

    public String[] getValues()
    {
        return values;
    }

    public void setValues(String[] values)
    {
        this.values = values;
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

}
