package org.lamport.tla.toolbox.spec.parser;

import java.util.Hashtable;
import java.util.List;
import java.util.Vector;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DoubleHashedTable
{
    private static final float DEFALT_THRESHOLD = 0.75f;
    private static final int DEFAULT_SIZE = 11;

    private Hashtable forwardStore = null;
    private Hashtable backwardStore = null;

    public DoubleHashedTable()
    {
        this(DEFAULT_SIZE, DEFALT_THRESHOLD);
    }

    public DoubleHashedTable(int size)
    {
        this(size, DEFALT_THRESHOLD);
    }

    public DoubleHashedTable(int size, float threshold)
    {
        forwardStore = new Hashtable(size, threshold);
        backwardStore = new Hashtable(size, threshold);
    }

    public void clear()
    {
        forwardStore.clear();
        backwardStore.clear();
    }

    public boolean containsKey(Object key)
    {
        return forwardStore.containsKey(key);
    }

    public boolean containsValue(Object value)
    {
        return forwardStore.containsValue(value);
    }

    public List getValues(Object key)
    {
        return (List) forwardStore.get(key);
    }

    public List getKeys(Object value)
    {
        return (List) backwardStore.get(value);
    }

    /**
     * Puts a key and a list of values in to the store. <br>
     * <b>Note:</b>The method will eliminate duplicate values in the list, if any
     * @param key the key 
     * @param values list of values
     * @return the previous stored list of values
     */
    public List put(Object key, List values)
    {
        if (values == null)
        {
            values = new Vector(0);
        }

        Vector listWithoutDoublicates = new Vector(values.size());

        for (int i = 0; i < values.size(); i++)
        {
            List keys = (List) backwardStore.get(values.get(i));
            if (keys == null)
            {
                keys = new Vector();
            }
            if (!keys.contains(key))
            {
                keys.add(key);
                listWithoutDoublicates.add(values.get(i));
                backwardStore.put(values.get(i), keys);
            }
        }
        return (List) forwardStore.put(key, listWithoutDoublicates);
    }

    /**
     * Removes the key with associated values
     * @param key
     * @return
     */
    public List removeKey(Object key)
    {
        return universalRemove(key, forwardStore, backwardStore);
    }

    /**
     * Removes the value with associated keys
     * @param value
     * @return
     */
    public List removeValue(Object value)
    {
        return universalRemove(value, backwardStore, forwardStore);
    }

    /**
     * Retrieves the number of stored keys
     * @return
     */
    public int size()
    {
        return forwardStore.size();
    }
    
    
    /**
     * Removes the toRemove from direct container (as a key with all values) and as all values from from inverted container  
     * @param toRemove element to remove
     * @param directContainer container, in that the element to remove is used as a key 
     * @param invertedContainer container, in that the element to remove is used as values
     * @return a list of dependents of given value
     */
    private static List universalRemove(Object toRemove, Hashtable directContainer, Hashtable invertedContainer)
    {
        List keys = (List) directContainer.remove(toRemove);
        if (keys != null)
        {
            for (int i = 0; i < keys.size(); i++)
            {
                Object key = keys.get(i);
                List values = (List) invertedContainer.get(key);
                if (values == null || !values.contains(toRemove))
                {
                    throw new RuntimeException("DoubleHashtable integrity violated");
                } else
                {
                    values.remove(toRemove);
                }
                // no put needed
            }
        }
        return keys;

    }
}
