/*******************************************************************************
 * Copyright (c) 2024 Linux Foundation. All rights reserved.
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
package tla2sany.api;

import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;

/**
 * Encapsulates information about a module's source code - the text itself,
 * and its origin (if applicable).
 */
public class ModuleSourceCode {

  /**
   * Possible locations from which a module can be read.
   */
  public enum ModuleOrigin {

    /**
     * The standard modules, embedded in this very JAR file.
     */
    STANDARD_MODULES,

    /**
     * Modules found as .tla files in the filesystem.
     */
    FILESYSTEM,

    /**
     * Modules found inside a JAR on the classpath.
     */
    JAR,

    /**
     * Modules provided directly to the API, as a string.
     */
    IN_MEMORY_STRING
  }

  /**
   * The text of the module; this is kept as a byte array, not a string,
   * to avoid unnecessary conversions. Currently, all producers and consumers
   * more readily work with an array of bytes. If a human-readable string is
   * desired (for advanced error reporting, for example) then the function
   * {@link ModuleSourceCode#getTextAsString} can be used.
   */
  private final byte[] text;

  /**
   * The origin of this module.
   */
  private final ModuleOrigin origin;

  /**
   * The path at which this module was found, if sourced from
   * {@link ModuleOrigin#FILESYSTEM}. Null otherwise.
   */
  private final Path path;

  /**
   * Constructs a new instance of the {@link ModuleSourceCode} class.
   *
   * @param text The source code text, as a byte array.
   * @param origin The module origin.
   * @param path The path to the module, if applicable.
   */
  public ModuleSourceCode(byte[] text, ModuleOrigin origin, Path path) {
    this.text = text;
    this.origin = origin;
    this.path = path;
  }

  /**
   * The text of this module's source code, as a UTF-8 encoded byte array.
   *
   * @return The module source code.
   */
  public byte[] getText() {
    return this.text;
  }

  /**
   * The origin of this module.
   *
   * @return The origin of this module.
   */
  public ModuleOrigin getOrigin() {
    return this.origin;
  }
  
  /**
   * The path associated with this module, if it was sourced from the file
   * system; otherwise null.
   *
   * @return The path associated with this module, if it has one.
   */
  public Path getPath() {
    return this.path;
  }

  /**
   * Interpret the module text as a UTF-8 encoded string.
   *
   * @return The module text as a UTF-8 encoded string.
   */
  public String getTextAsString() {
    return new String(this.text, StandardCharsets.UTF_8);
  }

  /**
   * Makes the module text available as a {@link ByteArrayInputStream}. This
   * stream can either be closed or not, it does not matter; the underlying
   * data is a byte array, not a file handle or anything else that needs to
   * be explicitly released.
   *
   * @return The module text, as a {@link ByteArrayInputStream}.
   */
  public ByteArrayInputStream getTextAsInputStream() {
    return new ByteArrayInputStream(this.text);
  }
}
