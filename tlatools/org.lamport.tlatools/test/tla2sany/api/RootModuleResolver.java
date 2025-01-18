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

import java.nio.file.Path;

/**
 * This is a convenience class to support the common approach of possessing a
 * path to a .tla file to use as a root module and wanting to search for its
 * dependencies in the same directory.
 */
public class RootModuleResolver implements Resolver {

  /**
   * The actual resolver that finds modules in the root module's directory.
   */
  private final DefaultResolver innerResolver;

  /**
   * The expected name of the root module.
   */
  public final String rootModuleName;

  @Override
  public ModuleSourceCode resolve(String moduleName) {
    return this.innerResolver.resolve(moduleName);
  }

  /**
   * Initializes a new instance of the {@link RootModuleResolver} class.
   *
   * @param rootModulePath The path to the root .tla module.
   */
  public RootModuleResolver(Path rootModulePath) {
    final Path parentDir = parentDirOf(rootModulePath);
    this.innerResolver = new DefaultResolver(parentDir);
    this.rootModuleName = expectedModuleName(rootModulePath);
  }

  /**
   * Given a filepath, find its parent directory; if the file is in the
   * current working directory, return the path to that directory.
   *
   * @param filepath A path to a file.
   * @return A path to the directory containing that file.
   */
  private static Path parentDirOf(Path filepath) {
    final Path parent = filepath.getParent();
    return null == parent ? Path.of(".") : parent;
  }

  /**
   * Given a module filename with a .tla suffix, extract the expected module
   * name. For example, Paxos.tla has the expected module name Paxos.
   *
   * @param filepath The path to a .tla file.
   * @return The expected module name.
   */
  private static String expectedModuleName(Path filepath) {
    final String filename = filepath.getFileName().toString();
    final String tlaSuffix = ".tla";
    if (filename.endsWith(tlaSuffix)) {
      return filename.substring(0, filename.length() - tlaSuffix.length());
    } else {
      throw new IllegalArgumentException("File must have .tla suffix: " + filepath.toString());
    }
  }
}
