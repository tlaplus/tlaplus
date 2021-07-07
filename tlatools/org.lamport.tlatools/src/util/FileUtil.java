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
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
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
     * Parses the directory path from a filename. If the filename
     * is already a basename, returns the empty string.
     */
    public static String parseDirname(String filename) {
        int lastSep = filename.lastIndexOf(separatorChar);
        if (lastSep == -1) {
            // No parent directory.
            return "";
        }
        return filename.substring(0, lastSep + 1);
    }

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

    public static void copyFile(final String fromName, final String toName) throws IOException {
    	copyFile(new File(fromName), new File(toName));
    }
    
    
    public static void copyFile(final File source, final File destination) throws IOException {
    	Files.copy(source.toPath(), destination.toPath(), StandardCopyOption.REPLACE_EXISTING);
    }

	/**
	 * Atomically replaces the file targetName with the file sourceName.
	 * @param sourceName
	 * @param targetName
	 * @throws IOException
	 */
	public static void replaceFile(String sourceName, String targetName) throws IOException {
		Files.move(new File(sourceName).toPath(), new File(targetName).toPath(), StandardCopyOption.REPLACE_EXISTING);
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
    	return makeMetaDir(new Date(), specDir, fromChkpt);
    }
    
    public static String makeMetaDir(Date date, String specDir, String fromChkpt)
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

		// MAK 07/2021: Flip the default from low-res time-stamp to high-res time-stamp.
		// The old default causes problems when TLC is invoked on a small spec in
		// scripts or e.g. bash while loops.
        SimpleDateFormat sdf;
        String highres = System.getProperty(FileUtil.class.getName() + ".milliseconds", "true");
        if (Boolean.valueOf(highres)) {
        	sdf = new SimpleDateFormat("yy-MM-dd-HH-mm-ss.SSS");
        } else {
        	// -Dutil.FileUtil.milliseconds=false
        	sdf = new SimpleDateFormat("yy-MM-dd-HH-mm-ss");
        }
        metadir += sdf.format(date);
        File filedir = new File(metadir);

        // ensure the non-existence
        Assert.check(!filedir.exists(), EC.SYSTEM_METADIR_EXISTS, filedir.getAbsolutePath());

        // ensure the dirs are created
        Assert.check(filedir.mkdirs(), EC.SYSTEM_METADIR_CREATION_ERROR, filedir.getAbsolutePath());

        return metadir;
    }

    public static NamedInputStream createNamedInputStream(String name, FilenameToStream resolver)
    {
        return FileUtil.createNamedInputStream(name, resolver, null);
    }

    public static NamedInputStream createNamedInputStream(String name, FilenameToStream resolver, NamedInputStream rootFileNis)
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
        if (name.toLowerCase().endsWith(TLAConstants.Files.TLA_EXTENSION))
        {
            name = name.substring(0, (name.length() - TLAConstants.Files.TLA_EXTENSION.length()));
        }

        // now name=/frob/bar/somemod

        // filename is a path ending with .tla
        // sourceFilename=/frob/bar/somemod
        sourceFileName = name + TLAConstants.Files.TLA_EXTENSION;

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
                ToolIO.out.println("***Internal error: Unable to create NamedInputStream in toIStream method");
            }
        }

        // Fall back and try loading the module from a monolithic spec (one big .tla
        // file consisting of multiple TLA+ modules and TLC configs).
        if (rootFileNis != null) {
            File rootSourceFile = rootFileNis.sourceFile();
            if (rootSourceFile != null) {
                try {
                    NamedInputStream nis = MonolithSpecExtractor.module(rootSourceFile, name);
                    return nis;
                } catch (IOException e) {
                }
            }
        }
        /**
         * August 2014 - TL
         * Added some breaking up of the error here.
         * Before it just returned null, no matter, if the file doesn't exist
         * or the file cannot be read and now some printouts into ToolIO.err is being done.
         * Also, information about the actual path it is looking into is being added to the message.
         */
        else if (sourceFile != null)
        {
          ToolIO.err.println("File does not exist: " + sourceFile.getAbsolutePath() +
              " while looking in these directories: " + resolver.getFullPath());
        }
        else
        {
          ToolIO.err.println("Cannot locate " + sourceFileName + " in path: " + resolver.getFullPath());
        }
        // TL - end of addition
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
     * @throws FileNotFoundException 
     */
    public static OutputStream newBFOS(String name) throws FileNotFoundException
    {
        try
        {
            return new FileOutputStream(new File(name));
        } catch (FileNotFoundException e)
        {
            ToolIO.out.println("Error: Unable to write to file " + name);
            throw e;
        }
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

	public static File createTempFile(final String fileName) {
		final File file;
		// Create the temp file in Java's temp dir unless TLC's metaDir has been set. The
		// latter won't be the case when SANY is invoked directly or during the early
		// startup phase of TLC.
		if (TLCGlobals.metaDir != null) {
			file = new File(TLCGlobals.metaDir + separatorChar + fileName);
		} else {
			final String tDir = System.getProperty("java.io.tmpdir");
			file = new File(tDir + separatorChar + fileName);
		}
		// Let's get rid of the file when TLC terminates.
		file.deleteOnExit();
		return file;
	}
	
	
	/**
	 * This is themed on commons-io-2.6's IOUtils.copyLarge(InputStream, OutputStream, byte[]) -
	 * 	once we move to Java9+, dump this usage in favor of InputStream.transferTo(OutputStream)
	 * 
	 * @return the count of bytes copied
	 */
	public static long copyStream(final InputStream is, final OutputStream os) throws IOException {
		final byte[] buffer = new byte[1024 * 4];
		long byteCount = 0;
		int n;
		final BufferedInputStream bis = (is instanceof BufferedInputStream) ? (BufferedInputStream)is
																			: new BufferedInputStream(is);
		final BufferedOutputStream bos = (os instanceof BufferedOutputStream) ? (BufferedOutputStream)os
																			  : new BufferedOutputStream(os);
		while ((n = bis.read(buffer)) != -1) {
			bos.write(buffer, 0, n);
			byteCount += n;
		}
		
		bos.flush();
		
		return byteCount;
	}
}
