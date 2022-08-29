package model;

import util.FilenameToStream;
import util.SimpleFilenameToStream;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;

public class InJarFilenameToStream extends SimpleFilenameToStream implements
        FilenameToStream {
    private static final String TMPDIR = System.getProperty("java.io.tmpdir");

    private final String prefix;

    public InJarFilenameToStream(final String prefix) {
        this.prefix = prefix;
    }

    @Override
    public File resolve(final String name, final boolean isModule) {
        try (final InputStream is = InJarFilenameToStream.class.getResourceAsStream(prefix + name)) {
            if (is != null) {
                final File sourceFile = new TLAFile(TMPDIR + File.separator + name, InJarFilenameToStream.class.getResource(prefix + name), false, this);
                sourceFile.deleteOnExit();

                try (final FileOutputStream fos = new FileOutputStream(sourceFile)) {

                    final byte[] buf = new byte[1024];
                    int len;
                    while ((len = is.read(buf)) > 0) {
                        fos.write(buf, 0, len);
                    }

                    return sourceFile;
                }
            }
        } catch (final IOException e) {
            // must not happen
            e.printStackTrace();
        }


        return super.resolve(name, isModule);
    }
}
