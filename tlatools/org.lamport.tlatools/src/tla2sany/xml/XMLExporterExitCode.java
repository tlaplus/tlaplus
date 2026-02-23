/*******************************************************************************
 * Copyright (c) 2026 The Linux Foundation. All rights reserved.
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
package tla2sany.xml;

/**
 * Enumerated possible failure/exit codes for the {@link XMLExporter}.
 */
public enum XMLExporterExitCode {

  /**
   * Used when all is well and no failures occurred.
   */
  OK (0),

  /**
   * Indicates command-line argument parsing failed.
   */
  ARGS_PARSING_FAILURE (1),

  /**
   * Indicates that parsing the root spec file or one of its imported modules
   * failed.
   */
  SPEC_PARSING_FAILURE (2),

  /**
   * Indicates that the XML output schema file (.xsd) that should be embedded
   * in the .jar file could not be found. This probably indicates a bug in
   * the build system that produced the final .jar file.
   */
  XML_CANNOT_FIND_EMBEDDED_SCHEMA_FILE (3),

  /**
   * {@link javax.xml.parsers.DocumentBuilder} can throw an exception in its
   * constructor; this enumerates that case. Should probably never happen.
   */
  XML_CONFIGURATION_FAILURE (4),

  /**
   * {@link javax.xml.transform.TransformerFactory#newTransformer()} can
   * throw an exception; this enumerates that case. Should probably never
   * happen.
   */
  XML_TRANSFORMATION_FAILURE (5),

  /**
   * Indicates that the exported XML does not satisfy the schema. This is a
   * bug in the XML exporting code, or the schema itself.
   */
  XML_SCHEMA_VALIDATION_FAILURE (6);

  private final int code;

  private XMLExporterExitCode(int code) {
    this.code = code;
  }

  /**
   * Gets the integer exit code.
   */
  public int code() {
    return this.code;
  }

  /**
   * Given a numerical code, derives this class's enumerated equivalent.
   * Throws {@link IllegalArgumentException} if the given code does not
   * correspond to a code in this enumeration.
   */
  public static XMLExporterExitCode fromCode(final int code) {
    for (XMLExporterExitCode exitCode : XMLExporterExitCode.values()) {
      if (exitCode.code == code) {
        return exitCode;
      }
    }

    throw new IllegalArgumentException(Integer.toString(code));
  }
}
