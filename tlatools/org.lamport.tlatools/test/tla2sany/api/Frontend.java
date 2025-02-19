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

import tla2sany.parser.ParseException;
import tla2sany.parser.TokenMgrError;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;

/**
 * A programmatic interface for the Syntactic ANalYzer (SANY) TLA⁺ parser.
 * This is intended to support three types of users:
 *
 * 1. Users who want a single simple function that parses a module and all
 *    its dependencies from a {@link Path} to a root module; these users will
 *    want the {@link Frontend#parse(String, Resolver, Errors)} method, by
 *    initializing a {@link RootModuleResolver} instance.
 *
 * 2. Users who want finer-grained control over the stages of the parsing
 *    process by calling a type-driven sequence of functions; these users
 *    will want to start at {@link Frontend#processSyntax(String, Resolver)},
 *    using a {@link RootModuleResolver} or {@link StringResolver} instance.
 *
 * 3. (TODO) Users who want to modify the parsing result in-memory after the
 *    ordinary parsing process is completed - adding modules, definitions,
 *    expressions, etc.
 *
 * The only implementation of this interface is {@link SANYFrontend}, although
 * it was made an interface to enable SANY consumers to isolate their code in
 * testing by injecting their own implementation if desired.
 */
public interface Frontend {

  /**
   * Runs the entire parsing sequence for the given root module, resolving
   * all dependencies and performing semantic- & level-checking.
   *
   * @param rootModuleName The name of the root module.
   * @param resolver Utility for resolving module names to source code.
   * @param log A log for non-fatal semantic errors.
   * @return A table of external modules, with root module marked.
   * @throws TokenMgrError if lexing fails for any module.
   * @throws ParseException if syntax processing fails for any module.
   * @throws AbortException on fatal semantic-checking errors.
   */
  public ExternalModuleTable parse(String rootModuleName, Resolver resolver, Errors log)
    throws TokenMgrError, ParseException, AbortException;

  /**
   * Checks the syntax of the given module and builds a parse tree from it.
   * Parse errors are output to {@link ToolIO#out}. Future work might switch
   * this to the {@link Errors} class for uniformity & improved testability.
   *
   * @param moduleName The name of the module on which to run syntax parsing.
   * @param resolver Utility for resolving the given module name.
   * @return A parse tree, or null if syntax error.
   * @throws TokenMgrError on lexing error in module.
   * @throws ParseException on syntax parsing error in module.
   */
  public ModuleSyntaxTree processSyntax(String moduleName, Resolver resolver)
    throws TokenMgrError, ParseException;

  /**
   * Given a root module's syntax tree, find all modules the root module
   * depends on and parse them; continue this process recursively to build
   * a table of dependencies parsed to the syntax level.
   *
   * If the given module does not import any modules, it is safe to call this
   * function with the resolver parameter set to null.
   *
   * @param root The root module syntax tree.
   * @param resolver Utility to resolve module names into source code.
   * @param log A log for non-fatal semantic errors.
   * @return A table of syntax parse trees, with root indicated.
   * @throws TokenMgrError on lexing error of a dependency.
   * @throws ParseException on syntax parsing error of a dependency.
   * @throws AbortException on detection of circular dependencies.
   */
  public DependencyTable resolveDependencies(ModuleSyntaxTree root, Resolver resolver, Errors log)
    throws TokenMgrError, ParseException, AbortException;

  /**
   * Performs semantic checking on a table of syntax tree dependencies,
   * resolving all identifiers to their corresponding definitions and
   * applying various semantic validation constraints.
   *
   * @param dependencyTable A table of modules parsed to syntax level.
   * @param log A log for non-fatal semantic errors.
   * @return A table of semantic parse trees, with root indicated.
   * @throws AbortException On non-recoverable semantic error.
   */
  public ExternalModuleTable processSemantics(DependencyTable dependencyTable, Errors log)
    throws AbortException;

  /**
   * Performs level-checking on the semantic parse tree, ensuring that
   * expression levels (constant, variable, action, behavior) conform to
   * rules and constraints across all parsed modules.
   *
   * @param modules A table of semantic parse trees, with root indicated.
   * @param log A log for non-fatal semantic errors.
   * @return Whether levels in semantic parse tree are correct.
   */
  public boolean checkLevel(ExternalModuleTable modules, Errors log);
}
