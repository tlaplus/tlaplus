package tlc2.tool.distributed;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.rmi.RemoteException;
import java.util.HashMap;
import java.util.Map;

import util.FilenameToStream;
import util.SimpleFilenameToStream;

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
public class RMIFilenameToStreamResolver extends SimpleFilenameToStream {

	private final TLCServerRMI server;
	private final Map<String, File> fileCache;
	private final String rndPrefix;
	
	public RMIFilenameToStreamResolver(TLCServerRMI aServer) {
		assert aServer != null;
		this.server = aServer;
		this.fileCache = new HashMap<String, File>();
		
		// create a temp directory for the current worker in the system tmpdir
		final String javaTempDir = System.getProperty("java.io.tmpdir");
		final File file = new File(javaTempDir + File.separator + System.currentTimeMillis());
		file.deleteOnExit();
		boolean mkdir = file.mkdir();
		assert mkdir == true;
		this.rndPrefix = file.getAbsolutePath();
	}

	/* (non-Javadoc)
	 * @see util.FilenameToStream#resolve(java.lang.String, boolean)
	 */
	@Override
	public File resolve(final String filename, final boolean isModule) {
		// try to resolve locally first
		File file = super.resolve(filename, isModule);
		
		// read the file from the server if local resolution has failed
		if(!file.exists()) {
			// strip off path
			final String name = new File(filename).getName();
			
			File tempFile = fileCache.get(name);
			
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
				file = writeToNewTempFile(name, bs);
				
				// add to local file cache
				fileCache.put(name, file);
			}
		}
		
		return file;
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
