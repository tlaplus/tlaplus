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

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import tla2sany.parser.SyntaxTreeNode;

/**
 * Encapsulates information about a module's syntax tree, including some
 * utility functions for querying basic information about it.
 *
 * TODO: These utility functions are definitely implemented elsewhere; they
 *       will need to be integrated with or replaced by the existing ones.
 */
public class ModuleSyntaxTree {

  /**
   * Information about the module's source code.
   */
  public final ModuleSourceCode source;

  /**
   * The root node of the module's syntax tree.
   */
  public final SyntaxTreeNode root;

  /**
   * Constructs a new instance of the {@link ModuleSyntaxTree} class.
   *
   * @param source Information about the module's source code.
   * @param root The root node of the module's syntax tree.
   */
  public ModuleSyntaxTree(ModuleSourceCode source, SyntaxTreeNode root) {
    this.source = source;
    this.root = root;
  }

  /**
   * Query the syntax tree to extract the name of this module.
   *
   * @return The module name, as a string.
   */
  public String getModuleName() {
    return this.root.getHeirs()[0].getHeirs()[1].toString();
  }

  /**
   * Find the list of all modules imported by this module, through either
   * EXTENDS or INSTANCE statements. This list is provided in order that the
   * module names are encountered in the file, with duplicates removed.
   *
   * @return A list of all modules imported by this module.
   */
  public List<String> getDependencies() {
    // {@link LinkedHashSet} removes duplicates but preserves insertion order
    Set<String> dependencies = new LinkedHashSet<String>();

    // First get modules imported with EXTENDS
    // Index 1 is the EXTENDS statement: EXTENDS Naturals, Sequences
    SyntaxTreeNode extensions = this.root.getHeirs()[1];
    // The zeroeth element of the heirs is the EXTENDS keyword itself
    for (int i = 1; i < extensions.getHeirs().length; i++) {
      SyntaxTreeNode extension = extensions.getHeirs()[i];
      dependencies.add(extension.getImage());
    }

    // Next get modules imported with INSTANCE
    // TODO

    return new ArrayList<String>(dependencies);
  }
}
