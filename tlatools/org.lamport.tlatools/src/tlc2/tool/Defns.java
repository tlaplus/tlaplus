// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:55 PST by lamport
//      modified on Sat Jun 30 10:05:29 PDT 2001 by yuanyu

package tlc2.tool;

import util.UniqueString;

import java.io.Serializable;

/**
 * The purpose of this class is to hold definitions.
 * The index of a definition in the array is stored in
 * the UniqueString, that holds the name of the operation.
 * <p>
 * <p>
 * There are two kinds of definitions stored in the table:
 * an OpDefNode or a TLC value. A java override method is
 * stored as a MethodValue.
 *
 * @author Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
// SZ 10.04.2009: This class is used only once in {@link Spec}
// class. There exist exactly one instance of it in runtime.
// there is no reason to have any static fields in it. 
public class Defns implements ToolGlobals, Serializable {
    private static final long serialVersionUID = -6385408029837446202L;
    private int defnIdx;
    private Object[] table;

    private int varCount;


    public Defns() {
        this.table = new Object[defnIdx + 32];
    }

    Defns(final Defns other) {
        this.varCount = other.varCount;
        this.defnIdx = other.defnIdx;
        this.table = new Object[other.table.length];
        System.arraycopy(other.table, 0, this.table, 0, other.table.length);
    }

    /**
     * Returns the definition of key if its definition exists.
     * Otherwise, returns null.
     */
    public Object get(final UniqueString key) {
        final int loc = key.getDefnLoc(varCount);
        if (loc < 0 || loc >= this.table.length) {
            return null;
        }
        return this.table[loc];
    }

    /**
     * Convenience method for {@link Defns#get(UniqueString)}
     */
    public Object get(final String key) {
        final UniqueString var = UniqueString.uniqueStringOf(key);
        return this.get(var);
    }

    /**
     * Store a new definition for key.  If there was an entry in the
     * table for the key, overwrite it.
     */
    public void put(final UniqueString key, final Object val) {
        int loc = key.getDefnLoc(varCount);
        if (loc == -1) {
            loc = defnIdx++;
            key.setLoc(loc);
        }
        if (loc >= this.table.length) {
            final int oldSize = this.table.length;
            final int newSize = Math.max(2 * oldSize, loc + 1);
            final Object[] old = this.table;
            this.table = new Object[newSize];
            // SZ 10.04.2009: changed a for loop of array copy to the 
            // native system copy call
            System.arraycopy(old, 0, this.table, 0, old.length);
        }
        this.table[loc] = val;
    }

    /**
     * Puts an object to the definitions
     *
     * @param key a string representation of the key
     * @param val the object to be stored
     */
    public void put(final String key, final Object val) {
        this.put(UniqueString.uniqueStringOf(key), val);
    }

    public void setDefnCount(final int index) {
        this.defnIdx = index;
        this.varCount = index;
    }

    public Defns snapshot() {
        return new Defns(this);
    }
}
