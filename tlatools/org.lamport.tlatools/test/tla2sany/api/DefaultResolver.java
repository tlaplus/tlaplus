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

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

import tla2sany.api.ModuleSourceCode.ModuleOrigin;

/**
 * This resolver encodes SANY's default behavior for finding modules. This
 * is currently only a prototype for testing purposes and needs to be
 * integrated with the {@link util.ResourceLocator} - which is what SANY
 * currently actually uses - by modifying those (& associated) classes to
 * return {@link ModuleSourceCode} instances.
 */
public class DefaultResolver implements Resolver {

  /**
   * An ordered list of directories in which to search for module files.
   */
  private final List<Path> searchPaths;

  @Override
  public ModuleSourceCode resolve(final String moduleName) {
    final String moduleFileName = moduleName + ".tla";

    // First: search through standard modules
    if (isStandardModule(moduleName)) {
      final String resourcePath = "/tla2sany/StandardModules/" + moduleFileName;
      try (final InputStream module = SANYFrontend.class.getResourceAsStream(resourcePath)) {
        if (null == module) {
          throw new RuntimeException("ERROR: Missing standard module " + moduleName);
        }
        final byte[] text = module.readAllBytes();
        return new ModuleSourceCode(text, ModuleOrigin.STANDARD_MODULES, Path.of(resourcePath));
      } catch (IOException e) {
        throw new RuntimeException("ERROR: Unable to read standard module " + moduleName);
      }
    }

    // Second: search in search directories
    for (final Path directory : this.searchPaths) {
      final Path modulePath = directory.resolve(moduleFileName);
      try (final InputStream module = new FileInputStream(modulePath.toFile())) {
        final byte[] text = module.readAllBytes();
        return new ModuleSourceCode(text, ModuleOrigin.FILESYSTEM, modulePath);
      } catch (IOException e) {
        continue;
      }
    }

    // Module could not be found
    // TODO: report this error using an exception
    return null;
  }

  /**
   * Construct a new instance of the {@link DefaultResolver} class.
   *
   * @param searchPaths Directories in which to search for modules.
   */
  public DefaultResolver(Path... searchPaths) {
    this.searchPaths = Arrays.asList(searchPaths);
  }

  /**
   * A list of all standard modules.
   */
  private static final String[] STANDARD_MODULES = new String[] {
    "Naturals",
    "Sequences",
    "FiniteSets",
    "TLC",
    "Bags",
    "Integers",
    "Reals",
    "Json",
    "Randomization",
    "RealTime",
    "TLCExt",
    "Toolbox"
  };

  /**
   * Whether the given name is the name of a standard module.
   *
   * @param moduleName The module name to check.
   * @return True if a standard module has the given name.
   */
  private static boolean isStandardModule(String moduleName) {
    for (String standardModule : STANDARD_MODULES) {
      if (moduleName.equals(standardModule)) {
        return true;
      }
    }
    return false;
  }
}
