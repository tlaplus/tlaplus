/*******************************************************************************
 * Copyright (c) 2003 Compaq Corporation. All rights reserved.
 * Copyright (c) 2003 Microsoft Corporation. All rights reserved.
 * Copyright (c) 2025 The Linux Foundation. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ******************************************************************************/
package util;

import java.io.ByteArrayInputStream;
import java.io.Closeable;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;

import tla2sany.api.ModuleSourceCode;
import tla2sany.api.ModuleSourceCode.ModuleOrigin;

/**
 * Fundamental class used to read TLA+ module source code. Despite the name,
 * it is not itself an {@link InputStream}. In the past it used to inherit
 * from {@link FileInputStream}, then was changed to simply read the file
 * while being constructed and keep it around as a {@link ModuleSourceCode}
 * instance wrapped by this class. This was motivated by a desire to decouple
 * the TLA+ tools from reliance on files instead of other methods of reading
 * in TLA+ modules, such as strings or files embedded inside jars. It was
 * also nice to avoid lifetime management issues and be able to read a module
 * multiple times.
 *
 * This class is currently in an intermediate phase where not all methods are
 * safe to call under all circumstances. Several methods exist under the
 * assumption that this class always refers to an underlying file with a
 * valid path, which in the future is hoped not to be the case. These methods
 * were written to function normally in the case that there *is* an actual
 * underlying file, which will be the case until the rest of the codebase is
 * changed to avoid using these methods and their implicit assumption of file
 * existence. The unsafe methods have all been marked as deprecated.
 */
public class NamedInputStream implements Closeable
{
    /**
     * A static field tracking the number of {@link NamedInputStream}
     * instances that have been created, minus the number that have had
     * {@link NamedInputStream#close()} called on them.
     */
    private static int numberOfReferences = 0;

    /**
     * The expected name of the module. This is not based on any analysis of
     * the module contents but comes from elsewhere, like if a module is
     * imported from another.
     */
    private final String moduleName;

    /**
     * Information about the contents and source of the TLA+ module. This
     * class is largely a legacy wrapper for it.
     */
    private final ModuleSourceCode source;

    /**
     * Initializes a new instance of the {@link NamedInputStream} class.
     * This constructor immediately reads in the given file and stores it in
     * a {@link ModuleSourceCode} instance for repeated later retrieval. It
     * also increments the static reference counter for this class.
     *
     * @param fileName The name of the TLA+ file to be read. Ignored.
     * @param moduleName The expected name of the module in the file.
     * @param inputFile The actual TLA+ file to read in and store.
     * @throws FileNotFoundException If the TLA+ file does not exist.
     * @throws IOException If there was an error reading the TLA+ file.
     */
    public NamedInputStream(String fileName, String moduleName, File inputFile) throws FileNotFoundException, IOException
    {
        this.moduleName = moduleName;
        try (InputStream input = new FileInputStream(inputFile)) {
          this.source = new ModuleSourceCode(
              input.readAllBytes(),
              ModuleOrigin.FILESYSTEM,
              inputFile.toPath());
        }

        synchronized (NamedInputStream.class)
        {
            if (NamedInputStream.numberOfReferences < 0)
            {
                NamedInputStream.numberOfReferences = 0;
            }

            NamedInputStream.numberOfReferences++;
        }
    }

    /**
     * Alias of {@link NamedInputStream#getFileName()}.
     *
     * @return The name of the file.
     */
    public final String getName()
    {
        return this.getFileName();
    }

    /**
     * Gets the name of the file read in by this class, if it was sourced
     * from the filesystem. Otherwise, synthesize the expected filename by
     * appending .tla onto the module name.
     *
     * @return The name of the file read in by this class.
     * @deprecated Avoid assuming TLA+ modules come from the filesystem.
     */
    @Deprecated(since = "1.8.0")
    public final String getFileName()
    {
        return
            this.source.getOrigin() == ModuleOrigin.FILESYSTEM
            ? this.source.getPath().getFileName().toString()
            : this.getModuleName() + TLAConstants.Files.TLA_EXTENSION;
    }

    /**
     * Gets the module name which was provided upon constructing the class.
     * This name was not derived from the module contents and could be wrong.
     *
     * @return The expected name of the module read in by this class.
     */
    public final String getModuleName()
    {
        return this.moduleName;
    }

    /**
     * If this module was sourced from the filesystem, return the path to
     * that file. Otherwise, return null.
     *
     * @return Path if applicable, null otherwise.
     * @deprecated Avoid assuming TLA+ modules come from the filesystem.
     */
    @Deprecated(since = "1.8.0")
    public final File sourceFile()
    {
        return
            this.source.getOrigin() == ModuleOrigin.FILESYSTEM
            ? this.source.getPath().toFile()
            : null;
    }

    /**
     * If this module was sourced from the filesystem, return the path to
     * that file in absolute resolved form. If the file was symlinked, this
     * resolves the final target. On Windows, works for mklink but not cygwin
     * symlinks. If the module was not sourced from the filesystem then
     * return null.
     *
     * @throws IOException If file does not exist or other I/O error occurs.
     * @deprecated Avoid assuming TLA+ modules come from the filesystem.
     */
    @Deprecated(since = "1.8.0")
    public final Path getAbsoluteResolvedPath() throws IOException {
        return
            this.source.getOrigin() == ModuleOrigin.FILESYSTEM
            ? this.source.getPath().toRealPath()
            : null;
    }

    @Override
    public final String toString()
    {
        return "[ fileName: " + this.getFileName() + ", moduleName: " + this.getModuleName() + " ]";
    }

    /**
     * Gets the {@link ByteArrayInputStream} instance containing the content
     * held by this class. Caller can close the input stream or not; for a
     * {@link ByteArrayInputStream}, closing it is a no-op.
     *
     * @return An {@link ByteArrayInputStream} with the module contents.
     */
    public ByteArrayInputStream getInputStream() {
      return this.source.getTextAsInputStream();
    }

    /**
     * Gets the {@link ModuleSourceCode} instance wrapped by this class.
     *
     * @return The source code wrapped by this class.
     */
    public ModuleSourceCode getSource() {
      return this.source;
    }

    /**
     * This method does not actually close any underlying input stream but
     * instead decrements a static reference counter for this class. Since
     * transitioning the class to wrap {@link ModuleSourceCode} there is no
     * {@link InputStream} instance that needs closing. Should be removed
     * once {@link NamedInputStream#getNumberOfreferences()} is deleted.
     */
    @Override
    public void close() throws IOException
    {
        synchronized (NamedInputStream.class)
        {
            NamedInputStream.numberOfReferences--;
        }
    }

    /**
     * Gets the recorded number of {@link NamedInputStream} instances that
     * have been constructed, minus the number that have been closed. It is
     * unclear what the purpose of this is; it does not seem to be in use and
     * was possibly used to debug lifetime management issues for file input
     * streams at some point. Good candidate for future removal, along with
     * the rest of the reference counting logic.
     *
     * @return The number of non-closed class instances constructed.
     * @deprecated Unused, also lifetime tracking is now much less important
     *             since no underlying {@link InputStream} actually needs to
     *             be closed.
     */
    @Deprecated(since = "1.8.0")
    public synchronized static int getNumberOfreferences()
    {
        return NamedInputStream.numberOfReferences;
    }
}
