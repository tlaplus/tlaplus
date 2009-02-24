// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package util;

import java.io.File;


/**
 * Resolver for the name to file handle
 * @author Leslie Lamport
 * @author Simon Zambrovski 
 * @version $Id$                                                      
 */
public interface FilenameToStream
{
    
    /**
     * This method resolves the logical name to the OS-resource 
     * @param filename
     * @param isModule
     * @return
     */
    public File resolve(String filename, boolean isModule);
}
