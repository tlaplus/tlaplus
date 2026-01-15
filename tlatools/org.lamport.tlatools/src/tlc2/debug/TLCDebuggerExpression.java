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
 *
 * Contributors:
 *   Andrew Helwer - code interfacing with SANY
 *   Markus Alexander Kuppe - code interfacing with TLC interpreter
 ******************************************************************************/
package tlc2.debug;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import tla2sany.output.SilentSanyOutput;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.Generator;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import tlc2.tool.impl.SpecProcessor;
import util.TLAConstants;
import util.ToolIO;
import util.UniqueString;

public abstract class TLCDebuggerExpression {
	
	private TLCDebuggerExpression() {
		// no instantiation.
	}

	/**
	 * Given a spec and an unparsed expression, build an operator that can be
	 * evaluated within the context of that spec.
	 *
	 * @param processor     Processes expression within the model context.
	 * @param semanticRoot  The root of the spec's semantic parse tree.
	 * @param location      The breakpoint location.
	 * @param conditionExpr The unparsed  expression.
	 * @return An expression, or null if parsing failed.
	 */
	public static OpDefNode process(final SpecProcessor processor, final ModuleNode semanticRoot,
			final Location location, final String conditionExpr) {
		final Set<String> paramNames = getScopedIdentifiers(semanticRoot, location);
		return process(processor, semanticRoot, paramNames, conditionExpr);
	}

	/**
	 * Given a spec and an unparsed expression, build an operator that can be
	 * evaluated within the context of that spec.
	 *
	 * @param processor     Processes expression within the model context.
	 * @param semanticRoot  The root of the spec's semantic parse tree.
	 * @param conditionExpr The unparsed  expression.
	 * @return An expression, or null if parsing failed.
	 */
	public static OpDefNode process(final SpecProcessor processor, final ModuleNode semanticRoot,
			final String conditionExpr) {
		return process(processor, semanticRoot, new HashSet<>(), conditionExpr);
	}

	private static OpDefNode process(final SpecProcessor processor, final ModuleNode semanticRoot,
			final Set<String> paramNames, final String conditionExpr) {
		if (null == conditionExpr || conditionExpr.isBlank()) {
			return null;
		}
		
		// Check if we have already parsed this expression before, or if it refers to an
		// existing operator.
		OpDefNode bpOp = semanticRoot.getOpDef(conditionExpr);
		if (bpOp != null) {
			return bpOp;
		}

		final String rootModName = semanticRoot.getName().toString();
		final String bpModName = semanticRoot.generateUnusedName("__DebuggerModule__%s");
		final String bpOpName = semanticRoot.generateUnusedName("__DebuggerExpr__%s");
		final String params = paramNames.size() > 0 ? "(" + String.join(", ", paramNames) + ")" : "";
		final String bpOpDef = bpOpName + params;

		final String wrapper = "---- MODULE %s ----\nEXTENDS %s\n%s == %s\n====";
		String wrappedConditionExpr = String.format(wrapper, bpModName, rootModName, bpOpDef, conditionExpr);
		byte[] wrappedConditionExprBytes = wrappedConditionExpr.getBytes(StandardCharsets.UTF_8);
		TLAplusParser parser = new TLAplusParser(new SilentSanyOutput(), wrappedConditionExprBytes);
		boolean syntaxParseSuccess = parser.parse();
		SyntaxTreeNode syntaxRoot = parser.ParseTree;
		if (!syntaxParseSuccess || null == syntaxRoot) {
			// Parse error is output to ToolIO.out
			ToolIO.err.println("Syntax error while parsing breakpoint expression \"" + conditionExpr + "\"");
			return null;
		}
		
		final ExternalModuleTable emt = processor.getModuleTbl();
		try {
			// Resolve dependencies not already resolved.
			resolveDependencies(processor, emt, Stream.of(parser.dependencies())
					.filter(dep -> emt.getModuleNode(dep) == null).collect(Collectors.toList()));
		} catch (AbortException e) {
			ToolIO.err.print(e.toString());
			ToolIO.err.println("Dependency error while parsing breakpoint expression \"" + conditionExpr + "\"");
			return null;
		}

		Errors semanticLog = new Errors();
		Generator semanticChecker = new Generator(emt, semanticLog);
		ModuleNode bpModule = null;
		try {
			bpModule = semanticChecker.generate(syntaxRoot);
		} catch (AbortException e) {
			ToolIO.err.print(e.toString());
			ToolIO.err.println("Semantic error while parsing breakpoint expression \"" + conditionExpr + "\"");
			return null;
		}
		if (null == bpModule || semanticLog.isFailure()) {
			ToolIO.err.print(semanticLog.toString());
			ToolIO.err.println("Semantic error while parsing breakpoint expression \"" + conditionExpr + "\"");
			return null;
		}

		// Run level-checking. The operator should be restricted to
		// action-level or below.
		Errors levelCheckingErrors = new Errors();
		boolean levelCheckingSuccess = bpModule.levelCheck(levelCheckingErrors);
		if (!levelCheckingSuccess || levelCheckingErrors.isFailure() || !bpModule.levelCorrect) {
			ToolIO.err.println(levelCheckingErrors.toString());
			ToolIO.err.println("Level-checking error while parsing breakpoint expression \"" + conditionExpr + "\"");
			return null;
		}
		
		bpOp = bpModule.getOpDef(bpOpName);
		if (null == bpOp) {
			ToolIO.err.println("ERROR: unable to find debugger expression op " + bpOpName);
			return null;
		}

		if (!(LevelConstants.ConstantLevel == bpOp.getLevel() || LevelConstants.VariableLevel == bpOp.getLevel()
				|| LevelConstants.ActionLevel == bpOp.getLevel())) {
			ToolIO.err.println("ERROR: Debug expressions must be action-level or below; actual level: "
					+ SemanticNode.levelToString(bpOp.getLevel()));
			return null;
		}

		processor.processConstantsDynamicExtendee(bpModule);
		
		processor.processModuleOverrides(bpModule, emt);
		
		return bpOp;
	}
	
	private static ExternalModuleTable resolveDependencies(final SpecProcessor processor, final ExternalModuleTable emt,
			final List<String> dependencies) throws AbortException {
		for (String moduleName : dependencies) {
			try (final InputStream moduleSource = new FileInputStream(
					ToolIO.getDefaultResolver().resolve(moduleName + TLAConstants.Files.TLA_EXTENSION, false))) {
				final TLAplusParser parser = new TLAplusParser(new SilentSanyOutput(), moduleSource);

				boolean syntaxParseSuccess = parser.parse();
				SyntaxTreeNode syntaxRoot = parser.ParseTree;
				if (!syntaxParseSuccess || null == syntaxRoot) {
					ToolIO.err.println("Syntax error while parsing breakpoint expression's dependency \"" + moduleName + "\"");
					continue;
				}

		        // Transitively resolve dependencies.
				for (String dep : parser.dependencies()) {
					if (emt.getModuleNode(dep) == null) {
						resolveDependencies(processor, emt, List.of(dep));
					}
				}

				final Errors log = new Errors();
				final Generator semanticParser = new Generator(emt, log);
				final ModuleNode module = semanticParser.generate(parser.rootNode());
				if (log.isFailure()) {
					ToolIO.err.print(log.toString());
					ToolIO.err.println("Semantic error while parsing breakpoint expression's dependency \"" + moduleName + "\"");
					continue;
				}
				module.levelCheck(log);
				// Process module's constants like numerals, strings, ...
				processor.processConstantsDynamicExtendee(module);
				emt.put(UniqueString.of(moduleName), semanticParser.getSymbolTable().getExternalContext(), module);
			} catch (IOException e) {
				throw new RuntimeException("ERROR: Unable to read module " + moduleName);
			}
		}
		return emt;
	}

	/**
	 * The expression operator can accept parameters; for example if we want
	 * to add a breakpoint at the following location:
	 *
	 * VARIABLE i
	 * op(j) ==
	 *   \A k \in S :
	 *     F(i, j, k) (* want to add breakpoint here)
	 *
	 * It would be nice for the user to just be able to type an expression
	 * like "i + j >= k"; however, there then arises the problem of how to take
	 * that expression and make it parse-able. Thus we end up auto-generating
	 * an operator that looks like:
	 *
	 * __BreakpointExpr__0(j, k) == i + j >= k
	 *
	 * Where we put the two scoped identifiers as parameters to the operator
	 * (note that we do not put the global identifier "i" as a parameter,
	 * because SANY would raise a parse error for multiple "i" definitions).
	 * Then, when evaluating the breakpoint expression we find those named
	 * values in the stack frame and plug them in. It is tricky but possible
	 * to isolate only the variables local to the breakpoint scope; that is
	 * what this function does.
	 *
	 * However, this gives rise to another problem; what if the user writes a
	 * spec like this?
	 *
	 * op(i) ==
	 *   \A j \in S :
	 *     F(i, j) (* want to add breakpoint here *)
	 * VARIABLE i
	 *
	 * Since when we extend the module so as to define our generated op it is
	 * implicitly parsed at the end of the file, "__BreakpointExpr__0(i, j)"
	 * will result in a parse error due to multiple "i" definitions.
	 * Currently these types of specs are simply not supported. Supporting
	 * them would probably require changes to the semantic analysis and
	 * constants-resolver code enabling parsing "ghost" definitions at
	 * arbitrary points in the tree.
	 *
	 * The way this method works is it first finds the parse tree node where
	 * the breakpoint was introduced, then traces its parentage up to the
	 * module root while recording identifiers produced by:
	 *  - LET/IN blocks
	 *  - Quantification operators
	 *  - Operator parameters
	 *
	 * There are probably others but we will add to this code as the need is
	 * discovered. A better solution would be to record this info in the
	 * semantic nodes during the semantic checking process but that will have
	 * to wait until we have good test coverage of it. It should be noted
	 * this information is already sort of recorded in the (private)
	 * OpApplNode.allParams field, but only if the given expression actually
	 * references an outside parameter. By the time the semantic analysis
	 * process has actually reached that stage it's too late to append the
	 * references to the operator definition node.
	 *
	 * @param semanticRoot The root node of the semantic parse tree.
	 * @param location     The breakpoint location.
	 * @return A list of local identifiers accessible at the given location.
	 */
	static Set<String> getScopedIdentifiers(ModuleNode semanticRoot, Location location) {
		final List<SemanticNode> path = semanticRoot.pathTo(location, false);
		return  getScopedIdentifiers(semanticRoot, path);
	}

	static Set<String> getScopedIdentifiers(ModuleNode semanticRoot, final List<SemanticNode> path) {
		final Set<SymbolNode> ids = getScopedSymbols(semanticRoot, path);
		// TLA+ does not support operator overloading, so an operator is uniquely
		// identified by its name alone. However, in our module generation logic, we
		// must also take the operator’s arity into account.
		//
		// Consider the following TLA+ snippet:
		//
		//		     SomeContext ==
		//		         LET max(a, b) == IF a > b THEN a ELSE b
		//		         IN max(1, 2) = 2
		//
		// Now assume the following breakpoint expression:
		//
		//		     max(3, 4) = 4
		//
		// When generating a module for the breakpoint expression, we must produce:
		//
		//		     __DebuggerExpr__123(max(_, _)) == max(3, 4) = 4
		//
		// If we were to generate:
		//
		//		     __DebuggerExpr__123(max) == max(3, 4) = 4
		//
		// this would result in a parse error, because the operator reference does not
		// specify the required arity.
		return ids.stream().map(node -> node.getName().toString()
				+ (node.getArity() == 0 ? "" : "(" + String.join(",", Collections.nCopies(node.getArity(), "_")) + ")"))
				.collect(Collectors.toSet());
	}

	static Set<SymbolNode> getScopedSymbols(ModuleNode semanticRoot, final List<SemanticNode> path) {
		final Set<SymbolNode> identifiers = new HashSet<>();
		// pathTo starts at breakpoint location then goes up to module root
		for (SemanticNode current : path) {
			// Extract i from LET i == 5 IN ...
			if (current instanceof LetInNode) {
				LetInNode node = (LetInNode)current;
				for (OpDefNode def : node.getLets()) {
					identifiers.add(def);
				}
			// Extract op, i, j, k from op(i, j, k) == ...
			// Note: will not extract "op" if is top-level definition
			} else if (current instanceof OpDefNode) {
				OpDefNode node = (OpDefNode)current;
				if (null == semanticRoot.getOpDef(node.getName())) {
					identifiers.add(node);
				}
				for (FormalParamNode param : node.getParams()) {
					identifiers.add(param);
				}
			// Extract i, j from \A i, j \in Nat : ...
			} else if (current instanceof OpApplNode) {
				OpApplNode node = (OpApplNode)current;
				for (FormalParamNode param : node.getQuantSymbolLists()) {
					identifiers.add(param);
				}
			// Extract i, j from LAMBDA i, j : ...
			} else if (current instanceof OpArgNode) {
				OpArgNode node = (OpArgNode)current;
				SymbolNode opSymbol = node.getOp();
				if (opSymbol instanceof OpDefNode) {
					OpDefNode op = (OpDefNode)opSymbol;
					for (FormalParamNode param : op.getParams()) {
						identifiers.add(param);
					}
				}
			}
		}
		return identifiers;
	}
}