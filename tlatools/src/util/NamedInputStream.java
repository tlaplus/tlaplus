// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package util;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

// SZ Feb 20, 2009: moved to util and reformatted

/**
 * A NamedInputStream is an InputStream together with a name.  The most
 * common such object o will be one that is the InputStream obtained by
 * reading a file named o.getName().
 *
 * It extends FileInputStream, rather than input stream, since it's not 
 * possible to change the default hierarchy. This implies that it isn't 
 * possible to use the same class for a buffer derived from an input string.
 * 
 * @author Leslie Lamport
 * @version $Id$
 */
public class NamedInputStream extends FileInputStream
{
    private String fileName;
    private String moduleName;
    private File inputFile;

    public NamedInputStream(String file, String module, File input) throws FileNotFoundException
    {
        super(input);
        fileName = file;
        moduleName = module;
        inputFile = input;
    }

    public final String getName()
    {
        return fileName;
    }

    public final String getFileName()
    {
        return fileName;
    }

    public final String getModuleName()
    {
        return moduleName;
    }

    public final File sourceFile()
    {
        return inputFile;
    }

    public final String toString()
    {
        return "[ fileName: " + fileName + ", moduleName: " + moduleName + " ]";
    }

}
