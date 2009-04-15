// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:55 PST by lamport
//      modified on Sat Jun 30 10:05:29 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.Serializable;

import util.UniqueString;

/**
 * The purpose of this class is to hold definitions.
 * The index of a definition in the array is stored in
 * the UniqueString, that holds the name of the operation.    
 * 
 * 
 * There are two kinds of definitions stored in the table:
 * an OpDefNode or a TLC value. A java override method is
 * stored as a MethodValue.
 * 
 * @author Yuan Yu, Simon Zambrovski
 * @version $Id$
 * 
 */
// SZ 10.04.2009: This class is used only once in {@link Spec}
// class. There exist exactly one instance of it in runtime.
// there is no reason to have any static fields in it. 
public class Defns implements ToolGlobals, Serializable
{
    private int defnIdx;
    private Object[] table;

    /**
     * Constructs the storage of initial size + 32
     */
    // SZ 10.04.2009: changed constructor to accept the initial 
    // value explicit during the object creation
    public Defns(int initialSize)
    {
        this.defnIdx = initialSize;
        this.table = new Object[defnIdx + 32];
    }

    public Defns()
    {
        this.table = new Object[defnIdx + 32];
    }

    /**
     * Returns the definition of key if its definition exists.
     * Otherwise, returns null.
     */
    public Object get(UniqueString key)
    {
        int loc = key.getDefnLoc();
        if (loc < 0 || loc >= this.table.length)
        {
            return null;
        }
        return this.table[loc];
    }

    /**
     * Convenience method for {@link Defns#get(UniqueString)} 
     * @param key
     * @return
     */
    public Object get(String key)
    {
        UniqueString var = UniqueString.uniqueStringOf(key);
        return this.get(var);
    }

    /**
     * Store a new definition for key.  If there was an entry in the
     * table for the key, overwrite it.
     */
    public void put(UniqueString key, Object val)
    {
        int loc = key.getDefnLoc();
        if (loc == -1)
        {
            loc = defnIdx++;
            key.setLoc(loc);
        }
        if (loc >= this.table.length)
        {
            int oldSize = this.table.length;
            int newSize = Math.max(2 * oldSize, loc + 1);
            Object[] old = this.table;
            this.table = new Object[newSize];
            // SZ 10.04.2009: changed a for loop of array copy to the 
            // native system copy call
            System.arraycopy(old, 0, this.table, 0, old.length);
        }
        this.table[loc] = val;
    }

    /**
     * Puts an object to the definitions
     * @param key a string representation of the key
     * @param val the object to be stored
     */
    public void put(String key, Object val)
    {
        this.put(UniqueString.uniqueStringOf(key), val);
    }

    public void setDefnCount(int index)
    {
        this.defnIdx = index;
    }
}
