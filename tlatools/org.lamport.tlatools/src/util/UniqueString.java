// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Wed Oct 17 15:25:39 PDT 2001 by yuanyu
package util;

import java.util.Hashtable;

import tlc2.tool.Defns;
import tlc2.tool.TLCState;

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
public final class UniqueString
{    
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
}
