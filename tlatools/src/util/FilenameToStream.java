// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package util;

import java.io.File;


/**
 * Resolver for the name to file handle.
 *
 * LL comment: 24 July 2013: I believe that the only classes that implements this
 * are SimpleFileNameToStream, RCPNameToFileIStream, and RMIFilenameToStreamResolver.
 * I added the isStandardModule method.
 *
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

      /**
       * August 2014 - TL
       * Added this method which returns all the path locations stored in the resolver
      */
    public String getFullPath();

    /**
     * Returns true iff moduleName is the name of a standard module, which
     * is identified by the directory in which its source file resides.
     *
     * @param moduleName
     * @return
     */
    public boolean isStandardModule(String moduleName) ;
    
	static final String TMPDIR = System.getProperty("java.io.tmpdir");

	static boolean isInJar(final String aString) {
		return aString.startsWith("jar:") || aString.endsWith(".jar");
	}

	static boolean isArchive(String aString) {
		return isInJar(aString) || aString.endsWith(".zip");
	}
}
