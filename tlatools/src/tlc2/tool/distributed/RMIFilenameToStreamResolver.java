package tlc2.tool.distributed;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.rmi.RemoteException;
import java.util.HashMap;
import java.util.Map;

import tlc2.output.MP;
import util.FilenameToStream;

/**
 * This class extends the SimpleFilenameToStream class in the way that it first
 * tries to resolve file with the local {@link FilenameToStream} resolver, but
 * falls back to RMI if the local resolver fails.
 * 
 * This is used for distributed TLC where a worker does not necessarily have
 * access to the specification and/or configuration files.
 * 
 * Care must be taken with transferring big files. This implementation is
 * inefficient in the way that it requires the server to read the full file into
 * memory before it gets transferred to the client. The client too, will buffer
 * the full file in memory. This constraint is acceptable for TLA specifications
 * and configurations as they are usually small enough to fit into memory "easily".
 */
public class RMIFilenameToStreamResolver implements FilenameToStream {

	private static final String javaTempDir = System.getProperty("java.io.tmpdir") + File.separator;

	private TLCServerRMI server;
	
	private final Map<String, File> fileCache = new HashMap<String, File>();
	private final String rndPrefix;
	
	public RMIFilenameToStreamResolver() {
		rndPrefix = getRandomStoragePrefix();
	}

	public RMIFilenameToStreamResolver(final String[] libraryPaths) {
		rndPrefix = getRandomStoragePrefix();
	}

	public void setTLCServer(final TLCServerRMI aServer) {
		this.server = aServer;
	}
	
	/* (non-Javadoc)
	 * @see util.FilenameToStream#resolve(java.lang.String, boolean)
	 */
	public File resolve(final String filename, final boolean isModule) {
		
		// read the file from the server
		// strip off path
		final String name = new File(filename).getName();
		
		File tempFile = fileCache.get(name);
		
		File file = null;
		// not in cache
		if (tempFile == null) {
			
			// read bytes from server
			byte[] bs = new byte[0];
			try {
				bs = server.getFile(name);
			} catch (RemoteException e) {
				e.printStackTrace();
			}

			// write into temp file
			file  = writeToNewTempFile(name, bs);
			
			// add to local file cache
			fileCache.put(name, file);
		}
		
		return file;
	}
	
	/**
	 * I am hoping that a resolver of this class is never used to parse
	 * the spec.  If it is, then a module's isStandard field will always
	 * be false in a run of distributed TLC.  This isn't a problem, since
	 * that field was added for use by a version of SANY called by TLAPS.
	 * 
	 * Added by LL on 24 July 2013.
	 */
	public boolean isStandardModule(String moduleName) {
		// The following error message code should be uncommented
		// if the parser should not be called with an object of
		// this class.
//		 String[] foo = new String[] {
//	       "Parsing called with unexpected FileNameToString implementation."} ;
//		 MP.printTLCBug(42, foo) ;
		 return false ;
	}

	private String getRandomStoragePrefix() {
		final File file = new File(javaTempDir + System.currentTimeMillis());
		file.deleteOnExit();
		file.mkdir();
		return file.getAbsolutePath();
	}
	
	private File writeToNewTempFile(String name, byte[] bs) {
		final File f = new File(rndPrefix + File.separator + name);
		f.deleteOnExit();
		
		FileOutputStream outputStream = null;
		try {
			outputStream = new FileOutputStream(f);
			outputStream.write(bs);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if(outputStream != null) {
				try {
					outputStream.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		return f;
	}
}
