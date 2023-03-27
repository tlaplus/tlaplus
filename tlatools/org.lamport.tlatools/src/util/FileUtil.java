// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, Oracle and/or its affiliates.

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
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
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
     * Determine the MetaDir to use.
     *
     * Equivalent to {@link #makeMetaDir(Date, String, String)} with
     * <code>date = new Date()</code>.  See that method for more details.
     *
     * @param specDir the specification directory
     * @param fromChkpt path of the checkpoints if recovering, or <code>null</code>
     * @return <code>fromChkpt</code> if it is not null, otherwise a new empty directory
     */
    public static String makeMetaDir(String specDir, String fromChkpt)
    {
    	return makeMetaDir(new Date(), specDir, fromChkpt);
    }

    /**
     * Determine the MetaDir to use.
     *
     * If <code>fromChkpt</code> is not null, then that directory is returned.
     * Otherwise, a new empty directory will be created and returned according
     * to the following rules:
     * <ol>
     *     <li>
     *         If {@link TLCGlobals#metaDir} is null, then a new empty
     *         directory in <code>specDir</code>/{@link TLCGlobals#metaRoot}
     *         will be created and returned.
     *     </li>
     *     <li>
     *         If {@link TLCGlobals#metaDir} is not null, then a new empty
     *         directory inside it will be created and returned.  The
     *         <code>specDir</code> argument is ignored in this case.
     *     </li>
     * </ol>
     * The new directory will use the given <code>date</code> in its name for
     * readability, but may include extra characters to ensure it is unique.
     *
     * <p>To ensure that concurrent processes do not accidentally share the
     * same MetaDir, if this method would create and return a new directory,
     * then the check for existence and creation happen as one atomic operation
     * as described in {@link Files#createDirectory}.
     *
     * @param date the date to use for naming the directory
     * @param specDir the specification directory
     * @param fromChkpt path of the checkpoints if recovering, or <code>null</code>
     * @return <code>fromChkpt</code> if it is not null, otherwise a new empty directory
     */
    public static String makeMetaDir(Date date, String specDir, String fromChkpt)
    {
        if (fromChkpt != null)
        {
            return fromChkpt;
        }

        Path metadir;
        if (TLCGlobals.metaDir != null) {
            metadir = Paths.get(TLCGlobals.metaDir);
        } else {
            // If not given, use the directory specDir/metaRoot:
            metadir = Paths.get(specDir).resolve(TLCGlobals.metaRoot);
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

        metadir = metadir.resolve(sdf.format(date));

        try {
            metadir = createExclusiveDirectoryWithApproximateName(metadir);
        } catch (IOException e) {
            Assert.fail(EC.SYSTEM_METADIR_CREATION_ERROR, metadir.toString());
        }

        return metadir.toString();
    }

    /**
     * Create the given directory and all required parent directories.
     * Identical to {@link Files#createDirectory}, but all missing
     * parent directories are created first.
     *
     * @param directory the directory to create
     * @throws FileAlreadyExistsException if the given directory already exists
     * @throws IOException if the given directory could not be created due
     *                     to some other error
     */
    public static void createExclusiveDirectory(Path directory) throws IOException {
        directory = directory.toAbsolutePath();
        Files.createDirectories(directory.getParent());
        Files.createDirectory(directory);
    }

    /**
     * Create and return a new directory.  The new directory will
     * have the same parent as <code>approximatePath</code>, but
     * may have a different name.
     *
     * @param approximatePath the approximate path and name of the
     *                        directory to create
     * @return the newly-created directory
     * @throws IOException if a new directory could not be created
     */
    public static Path createExclusiveDirectoryWithApproximateName(Path approximatePath) throws IOException {
        try {
            createExclusiveDirectory(approximatePath);
            return approximatePath;
        } catch (FileAlreadyExistsException e) {
            approximatePath = approximatePath.toAbsolutePath();
            return Files.createTempDirectory(approximatePath.getParent(), approximatePath.getFileName().toString());
        }
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

    /**
     * Find a safe place to write a temporary file with the given name.  To prevent
     * clashes with concurrent runs of other tools, this method creates a new
     * directory to contain the file. The file and directory will be marked for
     * cleanup using {@link File#deleteOnExit()}.
     *
     * <p>Note that after this method returns, the parent directory will exist but
     * the new file itself will not.  Callers are expected to create the actual file
     * themselves.
     *
     * @param fileName the name of the file to create
     * @return a {@link File} pointing to a location for the new file
     */
    public static File createTempFile(final String fileName) throws IOException {
        final File parentDirectory;
        final File file;

        // Create the temp file in Java's temp dir unless TLC's metaDir has been set. The
        // latter won't be the case when SANY is invoked directly or during the early
        // startup phase of TLC.
        if (TLCGlobals.metaDir != null) {
            parentDirectory = Files.createTempDirectory(Paths.get(TLCGlobals.metaDir), null).toFile();
        } else {
            parentDirectory = Files.createTempDirectory(null).toFile();
        }

        file = new File(parentDirectory, fileName);

        // Let's get rid of the file when TLC terminates.
        // Reminder: files will be deleted in the REVERSE of the order they are
        // registered using deleteOnExit().
        parentDirectory.deleteOnExit();
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
