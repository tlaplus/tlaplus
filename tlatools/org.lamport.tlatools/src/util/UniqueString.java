// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Wed Oct 17 15:25:39 PDT 2001 by yuanyu
package util;

import java.io.IOException;
import java.io.Serializable;
import java.util.Hashtable;
import java.util.Map;

import tlc2.tool.Defns;
import tlc2.tool.TLCState;
import tlc2.tool.distributed.InternRMI;
import tlc2.util.FP64;

/**
 * For any string (state variable, operator definition) the strings are stored 
 * only once for the entire run. This leads to a major speed-up in string comparison.<br>  
 * 
 * This class serves multiple purposes. 
 * <br><br>
 * 
 * The primary purpose is to use instances of this class as a wrapper or
 * data holder inside of the {@link InternTable}. The latter is organized that way, that it holds an
 * array of UniqueStrings. Each UniqueString that is created is put at most once into the table, and holds 
 * the information of its location in the table. The member variable {@link UniqueString#s} is used to represent 
 * the content, the member variable {@link UniqueString#tok} holds the position inside of the {@link InternTable}.
 * The following methods are responsible for access to content and position:
 * <ul>
 * </ul>
 * <br>
 * In addition, there exist two types of externally stored tables: the array of values of state variables 
 * in subclasses of {@link TLCState}, and array of operator definitions in {@link Defns}. The main scheme 
 * behind the storage of the objects in these arrays is that the value of a variable / operation 
 * definition with name, identified by a UniqueString <code>foo</code> is stored at position, in the array, that is 
 * stored inside of <code>foo</code>, using the instance member {@link UniqueString#loc}. Note, that multiple instances 
 * of TLCState store values of variables on the same position in their arrays and only one Defn instance 
 * exist. This is OK, because the state variable are global.
 * <br>
 * In order to distinguish between the index in the state variable array and index of operator definition array, 
 * the number of state variables defined in the specification is maintained in the static member {@link UniqueString#varCount}. 
 * The methods that are responsible for this feature are:
 * <ul>
 * </ul>
 * <br>
 * Finally, there are two methods responsible for marshaling/un-marshaling and convenience methods to put and get unique 
 * string into and out of the InternTable
 *  
 * @author Yuan Yu, Simon Zambrovski
 */
public final class UniqueString implements Serializable
{
    
    /** 
     * Maps from strings to variables. 
     */
    public static InternTable internTbl = null;
    /**
     * The string content
     */
    private String s;

    /** 
     * The unique integer assigned to the string.
     */
    private int tok;
    
    /**
     * Call static constructor method for call not out of TLC
     */
    static 
    {
        UniqueString.initialize();
    }

    /**
     * Static constructor method
     */
    public static void initialize()
    {
        internTbl = new InternTable(1024);
    }

    /**
     * Protected constructor, used from utility methods
     * @param str a string to be saved 
     * @param tok the unique integer for this string (position in the InternalTable)
     */
    protected UniqueString(String str, int tok)
    {
        this.s = str;
        this.tok = tok;
    }

    /**
     * Private constructor, used on marshaling/un-marshaling
     * @param str a string to be saved 
     * @param tok the unique integer for this string (position in the InternalTable)
     * @param loc location inside of the state/definition table
     */
    private UniqueString(String str, int tok, int loc)
    {
        this(str, tok);
        UniqueString.setVarLoc(str, loc);
    }
    
    // TODO: Move this to a different class. Eventually get rid of it.
    private static Hashtable<String, Integer> map = new Hashtable<>();
    /**
     * Returns the location of this variable in a state, if the name is a
     * variable.  Otherwise, returns -1.
     */
    public static int getVarLoc(String name) {
    	return map.get(name) == null ? -1 : map.get(name);
    }
    public static void setVarLoc(String name, int i) {
    	if (i < 0)
    		return;
    	map.put(name, i);
    }

    /**
     * Retrieves the unique number associated with this string
     * @return
     */
    public int getTok()
    {
        return this.tok;
    }
    
    /**
     * Not a compare method as usual for objects
     * Delivers the difference in positions inside of the table, the unique strings are stored in 
     * @param uniqueString
     * @return
     */
    public int compareTo(UniqueString uniqueString)
    {
        // SZ 10.04.2009: very strange way to compare strings
        // return this.s.compareTo(t.s);
        return this.tok - uniqueString.tok;
    }

    /**
     * Since uniqueness is guaranteed, the equals is a high performance reference comparison 
     */
    public boolean equals(UniqueString t)
    {
        return this.tok == t.tok;
    }

    /**
     * There is no performance gain to compare with a string.
     */
    public boolean equals(String t)
    {
        return this.s.equals(t);
    }

    /**
     * Returns a unique object associated with string str.  That is,
     * the first time uniqueStringOf("foo") is called, it returns a
     * new object o.  Subsequent invocations of uniqueStringOf("foo")
     * return the same object o.
     * 
     * This is a convenience method for a table put.
     */
    public static UniqueString uniqueStringOf(String str)
    {
        return internTbl.put(str);
    }

	public static UniqueString of(String str) {
		return uniqueStringOf(str);
	}


    /**
     * Writes current unique string to the stream
     * @param dos
     * @return
     * @throws IOException
     */
    public final void write(IDataOutputStream dos) throws IOException
    {
        dos.writeInt(this.tok);
        dos.writeInt(UniqueString.getVarLoc(this.toString()));
        dos.writeInt(this.s.length());
        dos.writeString(this.s);
    }

    /**
     * Utility method for reading a unique string from the stream
     * @param dis
     * @return
     * @throws IOException
     * 
     * The method does not change member/class variables
     */
    public static UniqueString read(IDataInputStream dis) throws IOException
    {
        int tok1 = dis.readInt();
        int loc1 = dis.readInt();
        int slen = dis.readInt();
        String str = dis.readString(slen);
        return new UniqueString(str, tok1, loc1);
    }
    
    public static UniqueString read(IDataInputStream dis, final Map<String, UniqueString> tbl) throws IOException
    {
        dis.readInt(); // skip, because invalid for the given internTbl
        dis.readInt(); // skip, because invalid for the given internTbl
        final int slen = dis.readInt();
        final String str = dis.readString(slen);
        return tbl.get(str);
    }


    /**
     * Sets the source 
     * @param source
     */
    public static void setSource(InternRMI source)
    {
        internTbl.setSource(source);
    }
}
