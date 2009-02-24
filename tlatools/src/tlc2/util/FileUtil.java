// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

import util.FilenameToStream;
import util.ToolIO;

/**
 * Utilities for file modifications
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FileUtil
{

    /**
     * Deletes the file or directory. Returns true iff the deletion
     * succeeds. The argument recurse forces the deletion of non-empty
     * directory.
     * @deprecated use {@link FileUtil#deleteDir(String, boolean)}
     */
    public static boolean deleteDir(File file, boolean recurse)
    {
        return doDeleteDir(file, recurse, ToolIO.getResolver());
    }
    
    /**
     * @deprecated don't use it
     * It is a bad implementation 
     */
    public static boolean deleteDir(String filename, boolean recurse)
    {
        return deleteDir(filename, recurse, ToolIO.getResolver());
    }

    public static boolean deleteDir(String filename, boolean recurse, FilenameToStream resolver)
    {
        return doDeleteDir(new File(filename), recurse, resolver);
    }
    
    /**
     * Implementation of the file deletion
     * @param file
     * @param recurse
     * @param resolver
     * @return
     */
    private static boolean doDeleteDir(File file, boolean recurse, FilenameToStream resolver)
    {
        if (file.exists())
        {
            if (file.isFile() || !recurse)
            {
                return file.delete();
            }
            // must be a directory:
            String[] fnames = file.list();
            File child = null;
            for (int i = 0; i < fnames.length; i++)
            {
                
                if (resolver == null) 
                {
                    child = new File(file, fnames[i]);
                } else {
                    // TODO
                }
                
                if (!doDeleteDir(child, recurse, resolver))
                {
                    return false;
                }
            }
            return file.delete();
        }
        return true;
    }
    


    /**
     * Constructs a input stream from the file
     * @param file
     * @param useGzip
     * @param useIBuffers
     * @param buffersize
     * @return
     * @throws IOException
     * SZ Feb 20, 2009: FileNotFoundException removed
     */
    public static InputStream newBZFileInputStream(String file, boolean useGzip, boolean useIBuffers, int buffersize)
            throws IOException
    {
        if (useGzip)
        {
            return new GZIPInputStream(new FileInputStream(file), buffersize);
        } else if (useIBuffers)
        {
            return new BufferedInputStream(new FileInputStream(file), buffersize);
        } else
        {
            return new FileInputStream(file);
        }
    }

    /**
     * Constructs an output stream to a file
     * @param file
     * @param useGzip
     * @param useOBuffers
     * @param buffersize
     * @return
     * @throws IOException
     */
    public static OutputStream newBZFileOutputStream(String file, boolean useGzip, boolean useOBuffers, int buffersize)
            throws IOException
    {
        return newBZFileOutputStream(file, useGzip, useOBuffers, buffersize, false);
    }

    /**
     * Constructs an output stream to a file
     * @param file
     * @param useGzip
     * @param useOBuffers
     * @param buffersize
     * @param append
     * 
     * @return
     * @throws IOException
     */
    public static OutputStream newBZFileOutputStream(String file, boolean useGzip, boolean useOBuffers, int buffersize,
            boolean app) throws IOException
    {
        if (useGzip)
        {
            return new GZIPOutputStream(new FileOutputStream(file, app), buffersize);
        } else if (useOBuffers)
        {
            return new BufferedOutputStream(new FileOutputStream(file, app), buffersize);
        } else
        {
            return new FileOutputStream(file, app);
        }
    }

    /**
     * Print array of big integers read from a input stream  
     * @param in
     * @throws IOException
     */
    public static void printArrayOfBigInts(InputStream in) throws IOException
    {
        BigInt[] A = ByteUtils.readSizeArrayOfSizeBigInts(in);
        for (int i = 0; i < A.length; i++)
        {
            ToolIO.out.println(A[i]);
        }
    }
    
    public static void copyFile(String fromName, String toName) throws IOException
    {
        // REFACTOR
        FileInputStream fis = new FileInputStream(fromName);
        FileOutputStream fos = new FileOutputStream(toName);
        byte[] buf = new byte[8192];
        int n;
        while ((n = fis.read(buf)) != -1)
        {
            fos.write(buf, 0, n);
        }
        fis.close();
        fos.close();
    }


}
