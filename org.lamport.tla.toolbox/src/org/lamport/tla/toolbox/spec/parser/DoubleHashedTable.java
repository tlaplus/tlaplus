package org.lamport.tla.toolbox.spec.parser;

import java.util.Hashtable;
import java.util.List;
import java.util.Vector;

/**
 * This was implemented by Simon to be used (and usable) only by the 
 * ParserDependencyStorage class.  It contains two Hashtables,
 * forwardStore and backwardStore, that are supposed to be used 
 * to determine dependency between modules.  I have no idea what
 * they are supposed to mean.  But debugging reveals that both of these
 * take as keys a String that is a user module name.  Each entry is 
 * a Vector of Strings, each of which is a user module name.
 * For a spec in which Test instantiates TestA which instantiates TestB,
 * they have the following entries:
 * <pre>
 *  backwardStore: [key |-> "TestA.tla", value |-> <<"Test.tla">>],
 *                 [key |-> "TestB.tla", value |-> <<"Test.tla">>],
 *                  
 *  forwardStore: [key |-> "Test.tla", value |-> <<"TestA.tla", "TestB.tla">>]
 * </pre>
 * A little further experimentation suggests that this is true in general:
 * backward store contains an entry for every non-root module pointing to the
 * root module, and forward store contains a single entry for the root module
 * pointing to the list of imported modules.
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
        return backwardStore.containsKey(value);
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
