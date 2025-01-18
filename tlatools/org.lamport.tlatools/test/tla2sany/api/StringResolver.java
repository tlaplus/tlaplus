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

import java.util.HashMap;
import java.util.Map;

import tla2sany.api.ModuleSourceCode.ModuleOrigin;

/**
 * A utility resolver for resolving modules as in-memory strings, usually for
 * use in test code.
 */
public class StringResolver implements Resolver {

  /**
   * A resolver to locate standard or other modules.
   */
  private final DefaultResolver innerResolver;

  /**
   * A collection of in-memory string modules.
   */
  private final Map<String, String> stringModules;

  @Override
  public ModuleSourceCode resolve(String moduleName) {
    final String stringModule = this.stringModules.get(moduleName);
    if (null == stringModule) {
      return this.innerResolver.resolve(moduleName);
    }
    return new ModuleSourceCode(
      stringModule.getBytes(),
      ModuleOrigin.IN_MEMORY_STRING,
      null);
  }

  /**
   * Initialize a new instance of the {@link StringResolver} class, for only
   * a single module.
   *
   * @param moduleName The name of the module.
   * @param moduleContents The contents of the module.
   */
  public StringResolver(String moduleName, String moduleContents) {
    this.innerResolver = new DefaultResolver();
    this.stringModules = new HashMap<String, String>();
    this.stringModules.put(moduleName, moduleContents);
  }

  /**
   * Initialize a new instance of the {@link StringResolver} class, for a set
   * of modules.
   *
   * @param modules The set of in-memory string modules.
   */
  public StringResolver(Map<String, String> modules) {
    this.innerResolver = new DefaultResolver();
    this.stringModules = modules;
  }
}
