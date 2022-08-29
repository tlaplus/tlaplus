package tlc2.tool.distributed;

import util.FilenameToStream;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.rmi.RemoteException;
import java.util.HashMap;
import java.util.Map;

/**
 * This class extends the SimpleFilenameToStream class in the way that it first
 * tries to resolve file with the local {@link FilenameToStream} resolver, but
 * falls back to RMI if the local resolver fails.
 * <p>
 * This is used for distributed TLC where a worker does not necessarily have
 * access to the specification and/or configuration files.
 * <p>
 * Care must be taken with transferring big files. This implementation is
 * inefficient in the way that it requires the server to read the full file into
 * memory before it gets transferred to the client. The client too, will buffer
 * the full file in memory. This constraint is acceptable for TLA specifications
 * and configurations as they are usually small enough to fit into memory "easily".
 */
public class RMIFilenameToStreamResolver implements FilenameToStream {

    private static final String javaTempDir = System.getProperty("java.io.tmpdir") + File.separator;
    private final Map<String, File> fileCache = new HashMap<>();
    private final String rndPrefix;
    private TLCServerRMI server;

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
    @Override
    public File resolve(final String filename, final boolean isModule) {

        // read the file from the server
        // strip off path
        final String name = new TLAFile(filename, this).getName();

        File file = fileCache.get(name);
        // not in cache
        if (file == null || !file.exists()) {

            // read bytes from server
            byte[] bs = new byte[0];
            try {
                bs = server.getFile(name);
            } catch (final RemoteException e) {
                e.printStackTrace();
            }

            // write into temp file
            file = writeToNewTempFile(name, bs);

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
     * <p>
     * Added by LL on 24 July 2013.
     */
    @Override
    public boolean isStandardModule(final String moduleName) {
        // The following error message code should be uncommented
        // if the parser should not be called with an object of
        // this class.
        return false;
    }

    private String getRandomStoragePrefix() {
        final File file = new File(javaTempDir + System.currentTimeMillis());
        file.deleteOnExit();
        file.mkdir();
        return file.getAbsolutePath();
    }

    private File writeToNewTempFile(final String name, final byte[] bs) {
        final File f = new TLAFile(rndPrefix + File.separator + name, this);
        f.deleteOnExit();

        try(final FileOutputStream outputStream = new FileOutputStream(f)) {
            outputStream.write(bs);
        } catch (final IOException e) {
            e.printStackTrace();
        }

        return f;
    }

    @Override
    public String getFullPath() {
        final StringBuilder buf = new StringBuilder();

        final String[] strings = fileCache.keySet().toArray(new String[0]);
        for (int i = 0; i < strings.length; i++) {
            final String string = strings[i];
            buf.append(string);
            if (i < string.length() - 1) {
                buf.append(", ");
            }
        }
        return buf.toString();
    }
}
