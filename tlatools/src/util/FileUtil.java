// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package util;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.util.BigInt;
import tlc2.util.ByteUtils;

/**
 * Utilities for file modifications
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FileUtil
{
    public static final char separatorChar = File.separatorChar;
    public static final String separator = File.separator;
    public static final String pathSeparator = File.pathSeparator;

    /**
     * Deletes the file or directory. Returns true iff the deletion
     * succeeds. The argument recurse forces the deletion of non-empty
     * directory.
     */
    public static boolean deleteDir(File file, boolean recurse)
    {
        return doDeleteDir(file, recurse);
    }

    /**
     * Convenience method 
     */
    public static boolean deleteDir(String filename, boolean recurse)
    {
        return doDeleteDir(new File(filename), recurse);
    }

    /**
     * Implementation of the file deletion
     * @param file
     * @param recurse
     * @param resolver
     * @return
     */
    private static boolean doDeleteDir(File file, boolean recurse)
    {
        if (file !=null && file.exists())
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
                child = new File(file, fnames[i]);

                if (!doDeleteDir(child, recurse))
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
    
    public static InputStream newZFileInputStream(String file) throws FileNotFoundException, IOException
    {
        return new GZIPInputStream(new FileInputStream(file));
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
    
    public static void printSizeArrayOfSizeBigIntegers(InputStream in) throws IOException {
        BigInteger[] A = ByteUtils.readSizeArrayOfSizeBigInts(in);
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

    
    /**
     * The MetaDir is fromChkpt if it is not null. Otherwise, create a
     * new one based on the current time.
     * @param specDir the specification directory
     * @param fromChkpt, path of the checkpoints if recovering, or <code>null</code>
     * 
     */
    public static String makeMetaDir(String specDir, String fromChkpt)
    {
        if (fromChkpt != null)
        {
            return fromChkpt;
        }
        String metadir = TLCGlobals.metaDir;
        if (metadir == null)
        {
            // If not given, use the directory specDir/metaRoot:
            metadir = specDir + TLCGlobals.metaRoot + FileUtil.separator;
        }

        SimpleDateFormat sdf = new SimpleDateFormat("yy-MM-dd-HH-mm-ss");
        metadir += sdf.format(new Date());
        File filedir = new File(metadir);
        
        // ensure the non-existence
        Assert.check(!filedir.exists(), EC.SYSTEM_METADIR_EXISTS, metadir);

        // ensure the dirs are created
        Assert.check(filedir.mkdirs(), EC.SYSTEM_METADIR_CREATION_ERROR, metadir);
        
        return metadir;
    }

    
    public static NamedInputStream createNamedInputStream(String name, FilenameToStream resolver)
    {
        // Strip off one NEWLINE and anything after it, if it is there
        int n;
        n = name.indexOf( '\n' );
        if ( n >= 0 ) {
            // SZ Feb 20, 2009: the message adjusted to what is actually done 
            ToolIO.out.println("*** Warning: module name '" + name + "' contained NEWLINE; "
                    + "Only the part before NEWLINE is considered.");
            name = name.substring( 0, n );     // Strip off the newline
        }

        
        String sourceFileName;
        String sourceModuleName;
        
        
        // consider name=/frob/bar/somemod.tla
        // or name=/frob/bar/somemod
        
        // Make sure the file name ends with ".tla".
        if (name.toLowerCase().endsWith(".tla")) 
        {
            name = name.substring(0, name.length() - 4);
        }
        
        // now name=/frob/bar/somemod
        
        // filename is a path ending with .tla
        // sourceFilename=/frob/bar/somemod
        sourceFileName = name + ".tla";

        // module name is =somemod
        sourceModuleName = name.substring(name.lastIndexOf(FileUtil.separator) + 1);

        File sourceFile = resolver.resolve(sourceFileName, true);
        if (sourceFile != null && sourceFile.exists())
        {
            try
            {
                NamedInputStream nis = new NamedInputStream(sourceFileName, sourceModuleName, sourceFile);
                return nis;
            } catch (FileNotFoundException e)
            {
                ToolIO.out.println("***Internal error: Unable to create NamedInputStream" + " in toIStream method");
            }
        }
        return null;
    }

    public static FileInputStream newFIS(File file)
    {
        if (file != null && file.exists())
        {
            try
            {
                FileInputStream fis = new FileInputStream(file);
                return fis;
            } catch (FileNotFoundException e)
            {
                ToolIO.out.println("***Internal error: Unable to create FileInputStream");
            }
        }
        return null;
    }
    public static FileOutputStream newFOS(File file)
    {
        if (file != null && file.exists())
        {
            try
            {
                FileOutputStream fos = new FileOutputStream(file);
                return fos;
            } catch (FileNotFoundException e)
            {
                ToolIO.out.println("***Internal error: Unable to create FileOutStream");
            }
        }
        return null;
    }

    
    /**
     * retrieves a new buffered file output stream
     * @param name
     * @return
     */
    public static OutputStream newBFOS(String name)
    {
        File file = new File(name);
        
        // LL removed file.exists() test on 10 Nov 2012 because
        // it causes an error when TLC called with -dump option
        // for a file that doesn't already exist.  Also changed
        // the error message to something more helpful.
        if (file != null /* && file.exists() */)
        {
            try
            {
                FileOutputStream fos = new FileOutputStream(file);
                return fos;
            } catch (FileNotFoundException e)
            {
                ToolIO.out.println("Error: Unable to write to file " + name);
            }
        }
        return null;
    }
    
    public static BufferedDataInputStream newBdFIS(boolean useGZIP, File file) throws IOException
    {
        if (useGZIP) 
        {
            return new BufferedDataInputStream(new GZIPInputStream(new FileInputStream(file)));   
        } else {
            return new BufferedDataInputStream(new FileInputStream(file));    
        }
    }

    /**
     * @param useGZIP
     * @param string
     * @return
     * @throws IOException 
     */
    public static BufferedDataInputStream newBdFIS(boolean useGZIP, String filename) throws IOException
    {
        return newBdFIS(useGZIP, new File(filename));
    }

    /**
     * @param b
     * @param poolFile
     * @return
     * @throws IOException 
     * @throws FileNotFoundException 
     */
    public static BufferedDataOutputStream newBdFOS(boolean useGZIP, File file) throws FileNotFoundException, IOException
    {
        if (useGZIP) 
        {
            return new BufferedDataOutputStream(new GZIPOutputStream(new FileOutputStream(file)));   
        } else {
            return new BufferedDataOutputStream(new FileOutputStream(file));    
        }
    }

    /**
     * @param useGZIP
     * @param string
     * @return
     * @throws IOException 
     */
    public static BufferedDataOutputStream newBdFOS(boolean useGZIP, String filename) throws IOException
    {
        return newBdFOS(useGZIP, new File(filename));
    }

    
    public static ObjectInputStream newOBFIS(File file) throws FileNotFoundException, IOException
    {
        return new ObjectInputStream(new BufferedInputStream(new FileInputStream(file)));
    }

    /**
     * @param chkptfile
     * @return
     * @throws IOException 
     * @throws FileNotFoundException 
     */
    public static ObjectInputStream newOBFIS(String filename) throws FileNotFoundException, IOException
    {
        return newOBFIS(new File(filename));
    }

    
    /**
     * @param poolFile
     * @return
     * @throws IOException 
     * @throws FileNotFoundException 
     */
    public static ObjectOutputStream newOBFOS(File file) throws FileNotFoundException, IOException
    {
        return new ObjectOutputStream(new BufferedOutputStream(new FileOutputStream(file)));
    }

    /**
     * @param tmpfile
     * @return
     * @throws IOException 
     * @throws FileNotFoundException 
     */
    public static ObjectOutputStream newOBFOS(String filename) throws FileNotFoundException, IOException
    {
        return newOBFOS(new File(filename));
    }

    /**
     * @param b
     * @param chkptName
     * @return
     * @throws FileNotFoundException 
     */
    public static DataInputStream newDFIS(String filename) throws FileNotFoundException
    {
        return new DataInputStream(new FileInputStream(new File(filename)));
    }

    /**
     * @param chkptName
     * @return
     * @throws FileNotFoundException 
     */
    public static DataOutputStream newDFOS(String filename) throws FileNotFoundException
    {
        return new DataOutputStream(new FileOutputStream(new File(filename)));
    }






}
