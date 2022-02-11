// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:55 PST by lamport
//      modified on Sat Jun 30 10:05:29 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

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
public class Defns implements Serializable // TODO: check whether this needs to implement Serializable
{
    private Map<String, Object> table;

    /**
     * Constructs the storage of initial size + 32
     */
    // SZ 10.04.2009: changed constructor to accept the initial 
    // value explicit during the object creation
    public Defns(int initialSize)
    {
        this.table = new HashMap<String,Object>(initialSize);
    }

    public Defns()
    {
        this.table = new HashMap<String,Object>();
    }

    Defns(Defns other) {
    	this.table = new HashMap<String,Object>(other.table);
    }
    
    /**
     * Returns the definition of key if its definition exists.
     * Otherwise, returns null.
     * @deprecated
     */
    public Object get(UniqueString key)
    {
    	return this.get(key.toString());
    }

    /**
     * Convenience method for {@link Defns#get(UniqueString)} 
     * @param key
     * @return
     */
    public Object get(String key)
    {
        return this.table.get(key);
    }

    /**
     * Store a new definition for key.  If there was an entry in the
     * table for the key, overwrite it.
     * @deprecated
     */
    public void put(UniqueString key, Object val)
    {
    	this.put(key.toString(), val);
    }

    /**
     * Puts an object to the definitions
     * @param key a string representation of the key
     * @param val the object to be stored
     */
    public void put(String key, Object val)
    {
        this.table.put(key, val);
    }

    /**
     * 
     * @param index
     * @deprecated
     */
    public void setDefnCount(int index)
    {
    }
    
    public Defns snapshot() {
    	return new Defns(this);
    }
}
