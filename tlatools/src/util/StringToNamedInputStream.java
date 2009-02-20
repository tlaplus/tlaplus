// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package util;


/**
 * Resolver for the name to Input Stream
 * (See the FrontEnd class's parseStream method for 
 * how it is used.)
 * @author Leslie Lamport
 * @author Simon Zambrovski 
 * @version $Id$                                                      
 */
public interface StringToNamedInputStream
{
    /**
     * Retrieves an input stream from the module name
     * @param name logical name
     * @return FIS or null, if file not found
     */
    public NamedInputStream toIStream(String name);

    /**
     * Retrieves an input stream from the file name
     * @param name logical name
     * @param isModule, if true, looks for TLA+ module
     * @return Input Stream or null, if file <code>not</code> found
     */
    public NamedInputStream toIStream(String name, boolean isModule);
}
