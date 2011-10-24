package org.lamport.tlatools.impl.distributed;

import java.io.File;
import java.io.IOException;

import tlc2.tool.distributed.RMIFilenameToStreamResolver;
import util.FilenameToStream;

public class OSGiNameToFileIStream extends RMIFilenameToStreamResolver implements FilenameToStream {

	/**
	 * The OSGi symbolic name of the tlatools bundle (this is defined in
	 * tlatools/META-INF/MANIFEST.MF)
	 */
	private static final String TLA_BUNDLE_NAME = "org.lamport.tlatools";

	public OSGiNameToFileIStream() throws IOException {
		super(initInternalLibraryPath());
	}

	/**
	 * Initialization of RCP internal location of standard modules
	 * @throws IOException 
	 */
	private static String[] initInternalLibraryPath() throws IOException {
		return TLCWorkerActivator.getEntries(TLA_BUNDLE_NAME, File.separator, STANDARD_MODULES_FOLDER);
	}
}
