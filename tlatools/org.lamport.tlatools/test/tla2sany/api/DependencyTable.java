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
import java.util.List;
import java.util.Map;

/**
 * A table of module syntax trees, along with each module's dependencies.
 */
public class DependencyTable {

  /**
   * The name of the root module, on which no other module depends.
   */
  public final String rootModuleName;

  /**
   * A mapping from module names to syntax trees.
   */
  public final Map<String, ModuleSyntaxTree> modules;

  /**
   * The modules depended upon by each module.
   */
  public final Map<String, List<String>> dependencies;

  /**
   * Constructs a new instance of the {@link DependencyTable} class. Only
   * sets the name of the root module and adds the root module to the table
   * of modules, does not perform any dependency resolution.
   *
   * @param root The syntax tree of the root module.
   */
  public DependencyTable(ModuleSyntaxTree root) {
    this.rootModuleName = root.getModuleName();
    this.modules = new HashMap<String, ModuleSyntaxTree>();
    this.modules.put(root.getModuleName(), root);
    this.dependencies = new HashMap<String, List<String>>();
  }
}
