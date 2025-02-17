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
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import tla2sany.parser.ParseException;
import tla2sany.parser.TLAplusParser;
import tla2sany.parser.TokenMgrError;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Context;
import tla2sany.semantic.ErrorCode;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.Generator;
import tla2sany.semantic.ModuleNode;
import tla2sany.st.Location;
import util.ToolIO;
import util.UniqueString;

/**
 * An implementation of the {@link Frontend} using SANY's existing syntax
 * parser along with its semantic & level checkers.
 */
public class SANYFrontend implements Frontend {

  @Override
  public ExternalModuleTable parse(
    String rootModuleName,
    Resolver resolver,
    Errors log
  ) throws TokenMgrError, ParseException, AbortException {
    final ModuleSyntaxTree syntaxRoot = this.processSyntax(rootModuleName, resolver);
    final DependencyTable dependenciesRoot = resolveDependencies(syntaxRoot, resolver, log);
    final ExternalModuleTable modules = processSemantics(dependenciesRoot, log);
    if (log.isFailure()) {
      ToolIO.err.println(log.toString());
      return null;
    }
    boolean levelOk = checkLevel(modules, log);
    if (!levelOk || log.isFailure()) {
      ToolIO.err.println(log.toString());
      return null;
    }
    return modules;
  }

  @Override
  public ModuleSyntaxTree processSyntax(
    String moduleName,
    Resolver resolver
  ) throws TokenMgrError, ParseException {
    final ModuleSourceCode source = resolver.resolve(moduleName);
    final InputStream input = new ByteArrayInputStream(source.text);
    final TLAplusParser parser = new TLAplusParser(input, StandardCharsets.UTF_8.name());
    return new ModuleSyntaxTree(source, parser.CompilationUnit());
  }

  @Override
  public DependencyTable resolveDependencies(
    final ModuleSyntaxTree root,
    final Resolver resolver,
    final Errors log
  ) throws TokenMgrError, ParseException, AbortException {
    final DependencyTable dependencyTable = new DependencyTable(root);
    final List<String> incompleteModules = new ArrayList<String>();
    incompleteModules.add(root.getModuleName());
    resolveDependencies(root.getModuleName(), dependencyTable, resolver, log, incompleteModules);
    return dependencyTable;
  }

  /**
   * Recursively resolves all dependencies of the given module name then
   * parses them to the syntax level, checking for circular dependencies.
   * Updates the dependency table in-place.
   *
   * @param moduleName Module name for which to resolve dependencies.
   * @param dependencyTable A table of dependencies parsed to syntax level.
   * @param resolver Utility to resolve module names into source code.
   * @param log A log for non-fatal semantic errors.
   * @param incompleteModules Modules with dependencies not fully resolved.
   * @throws TokenMgrError on lexing error of a dependency.
   * @throws ParseException on syntax parsing error of a dependency.
   * @throws AbortException on detection of circular dependencies.
   */
  private void resolveDependencies(
    String moduleName,
    DependencyTable dependencyTable,
    Resolver resolver,
    Errors log,
    List<String> incompleteModules
  ) throws TokenMgrError, ParseException, AbortException {
    final ModuleSyntaxTree module = dependencyTable.modules.get(moduleName);
    final List<String> dependencies = module.getDependencies();
    dependencyTable.dependencies.put(module.getModuleName(), dependencies);
    for (final String dependencyName : dependencies) {
      if (incompleteModules.contains(dependencyName)) {
        // TODO: reconstruct dependency chain for error message
        log.addAbort(
          ErrorCode.MODULE_DEPENDENCIES_ARE_CIRCULAR,
          Location.nullLoc,
          "Circular dependency detected",
          true
        );
      }
      if (!dependencyTable.modules.containsKey(dependencyName)) {
        final ModuleSyntaxTree dependency = this.processSyntax(dependencyName, resolver);
        dependencyTable.modules.put(dependency.getModuleName(), dependency);
        final List<String> incompleteModulesNext = new ArrayList<String>(incompleteModules);
        incompleteModulesNext.add(dependencyName);
        resolveDependencies(dependencyName, dependencyTable, resolver, log, incompleteModulesNext);
      }
    }
  }

  @Override
  public ExternalModuleTable processSemantics(
    DependencyTable dependencyTable,
    Errors log
  ) throws AbortException {
    // This line is an annoying incantation resetting static global state
    // that will hopefully be made unnecessary in the future.
    Context.reInit();
    final ExternalModuleTable mt = new ExternalModuleTable();
    final ModuleNode root = processSemantics(dependencyTable.rootModuleName, dependencyTable, log, mt);
    mt.setRootModule(root);
    return mt;
  }

  /**
   * Fills out the {@link ExternalModuleTable} with semantic parse trees of
   * all dependencies of the given module, recursively.
   *
   * @param moduleName The module to perform semantic analysis on.
   * @param dependencyTable A table of dependencies parsed to syntax level.
   * @param log A log for non-fatal semantic errors.
   * @param mt A table of dependencies parsed to semantic level.
   * @return The given module name parsed to semantic level.
   * @throws AbortException on fatal semantic-checking errors.
   */
  private ModuleNode processSemantics(
    String moduleName,
    DependencyTable dependencyTable,
    Errors log,
    ExternalModuleTable mt
  ) throws AbortException {
    for (final String dependencyName : dependencyTable.dependencies.get(moduleName)) {
      if (null == mt.getModuleNode(dependencyName)) {
        processSemantics(dependencyName, dependencyTable, log, mt);
      }
    }
    final Generator gen = new Generator(mt, log);
    final ModuleSyntaxTree parseTree = dependencyTable.modules.get(moduleName);
    final ModuleNode semanticRoot = gen.generate(parseTree.root);
    mt.put(UniqueString.of(moduleName), gen.getSymbolTable().getExternalContext(), semanticRoot);
    return semanticRoot;
  }

  @Override
  public boolean checkLevel(ExternalModuleTable mt, Errors log) {
    boolean levelOk = mt.getRootModule().levelCheck(log);
    return levelOk && log.isSuccess();
  }
}
