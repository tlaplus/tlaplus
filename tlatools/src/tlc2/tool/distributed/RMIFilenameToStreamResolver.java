package tlc2.tool.distributed;

import java.io.File;
import java.rmi.RemoteException;

import util.FilenameToStream;
import util.SimpleFilenameToStream;

/**
 * This class extends the SimpleFilenameToStream class in the way that it first
 * tries to resolve file with the local {@link FilenameToStream} resolver, but
 * falling back to RMI if the local resolver fails.
 * 
 * This is used for distributed TLC where a worker does not necessarily has
 * access to the specification and/or configuration files.
 * 
 * Care must be taken with transferring big files. This implementation is
 * inefficient in the way that it requires the server to read the full file into
 * memory before it gets transferred to the client. The client too, will buffer
 * the full file in memory. This constraint is acceptable for TLA specifications
 * and configurations as they are usually small.
 */
public class RMIFilenameToStreamResolver extends SimpleFilenameToStream {

	private TLCServerRMI server;

	public RMIFilenameToStreamResolver(TLCServerRMI server) {
		this.server = server;
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
			try {
				return server.getFile(filename);
			} catch (RemoteException e) {
				e.printStackTrace();
			}
		}
		
		return file;
	}
}
