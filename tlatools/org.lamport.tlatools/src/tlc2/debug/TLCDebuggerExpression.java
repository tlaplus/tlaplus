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
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import tla2sany.drivers.SemanticException;
import tla2sany.output.SilentSanyOutput;
import tla2sany.parser.ParseException;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.ErrorCode;
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
	 * @param conditionExpr The unparsed  expression.
	 * @return An expression, or null if parsing failed.
	 * @throws ParseException if syntax parsing fails.
	 * @throws SemanticException if semantic analysis or level-checking fails.
	 * @throws AbortException if dependency resolution fails.
	 */
	public static OpDefNode process(final SpecProcessor processor, final ModuleNode semanticRoot,
			final String conditionExpr) 
			throws ParseException, SemanticException, AbortException {
		return process(processor, semanticRoot, Location.nullLoc, conditionExpr);
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
	 * @throws ParseException if syntax parsing fails.
	 * @throws SemanticException if semantic analysis or level-checking fails.
	 * @throws AbortException if dependency resolution fails.
	 */
	public static OpDefNode process(final SpecProcessor processor, final ModuleNode semanticRoot,
			final Location location, final String conditionExpr) 
			throws ParseException, SemanticException, AbortException {
		if (null == conditionExpr || conditionExpr.isBlank()) {
			return null;
		}
		
		// Check if we have already parsed this expression before, or if it refers to an
		// existing operator.
		OpDefNode bpOp = semanticRoot.getOpDef(conditionExpr);
		if (bpOp != null) {
			return bpOp;
		}

		/*
		 * The *list scope* contains all semantic nodes from the user’s current location
		 * up to the root of module **M**. From these nodes, we extract the identifiers
		 * that may legally appear in the user’s debug expression and make them
		 * available to an expression that will be generated in a separate module **D**.
		 * 
		 * This extraction proceeds in two stages.
		 * 
		 * Stage 1: Identifiers requiring special handling (LET definitions)
		 * 
		 * In the first stage, we collect identifiers that require special treatment —
		 * specifically, `LET` definitions. Consider the following specification
		 * snippet. The user places a breakpoint on the line containing `IN` and wants
		 * to evaluate the debug expression `foo(2)`:
		 * 
		 *        ---- MODULE M ----
		 *        
		 *        VARIABLE v
		 *        
		 *        SomeAction(p, Op(_,_)) ==
		 *           LET foo(idx) == v[idx]
		 *           IN foo(1) + Op(6,7) ...
		 *           
		 *        ====
		 * 
		 * If we handled LET definitions in the same way as all other identifiers, we
		 * would turn foo into a parameter of the generated debug expression. However,
		 * this would require manually wiring the FormalParameterNode of __DebugExpr
		 * to the OpDefNode of the `foo(idx)` definition. This approach is error-prone
		 * and brittle.
		 * 
		 *        ---- MODULE D ----
		 *        EXTENDS M
		 *        
		 *        __DebugExpr(foo(_)) ==
		 *            foo(2)
		 *        
		 *        ====
		 * 
		 * Instead, we take a different approach. We generate a *stub definition* for
		 * the foo(idx) function directly in module **D**. This stub allows the
		 * OpDefNode of __DebugExpr to be cleanly connected to the original
		 * OpDefNode of foo(idx). This solution is straightforward, robust, and
		 * reuses existing infrastructure (specifically, ModuleNode#substituteFor,
		 * described below).
		 * 
		 * To avoid polluting the global scope or introducing naming conflicts, the stub
		 * definition is declared LOCAL to module D. Its body is simply TRUE, which
		 * makes the definition syntactically valid. The body itself is never evaluated.
		 * Interestingly, using a new LET definition instead of a LOCAL definition does 
		 * not work, presumably due to limitations in ModuleNode#substituteFor.
		 * 
		 *        ---- MODULE D ----
		 *        EXTENDS M
		 *        
		 *        LOCAL foo(idx) == TRUE
		 *        
		 *        __DebugExpr ==
		 *           foo(2)
		 *           
		 *        ====
		 */ 
		final List<SemanticNode> scope = semanticRoot.pathTo(location, false);
		
		// LET definitions for scoped identifiers.
		final Set<OpDefNode> letDefs = scope.stream().filter(LetInNode.class::isInstance).map(LetInNode.class::cast)
				.flatMap(node -> Arrays.stream(node.getLets())).collect(Collectors.toSet());

		// Build LET expression stubs: LOCAL foo(idx) == TRUE
		final String letExpr = letDefs.isEmpty() ? ""
				: letDefs.stream().map(def -> "LOCAL " + def.getSignature() + " == TRUE")
						.collect(Collectors.joining("\n", "", "\n"));

		/*
		 * Stage 2: All remaining identifiers
		 * 
		 * In the second stage, we collect all other identifiers that may appear in the
		 * user’s expression and add them as parameters to the FormalParameterNode of
		 * __DebugExpr.
		 * 
		 * This step is mostly straightforward, with one important caveat: we must
		 * preserve the arity of the original definitions (e.g., operators with
		 * parameters).
		 * 
		 * Variables and constants require no special handling, since they are global
		 * and module D extends module M.
		 * 
		 *       ---- MODULE D ----
		 *       EXTENDS M
		 *       
		 *       LOCAL foo(idx) == TRUE
		 *       
		 *       __DebugExpr(p, Op(_,_)) == 
		 *           foo(2)
		 *     
		 *       ====
		 */		
		final Set<SymbolNode> identifiers = getScopedSymbols(semanticRoot, scope);
		final Set<UniqueString> letNames = letDefs.stream().map(OpDefNode::getName).collect(Collectors.toSet());
		identifiers.removeIf(id -> letNames.contains(id.getName()));
		final Set<String> paramNames = identifiers.stream().map(node -> node.getName().toString()
				+ (node.getArity() == 0 ? "" : "(" + String.join(",", Collections.nCopies(node.getArity(), "_")) + ")"))
				.collect(Collectors.toSet());

		final String rootModName = semanticRoot.getName().toString();
		final String bpModName = semanticRoot.generateUnusedName("__DebuggerModule__%s");
		final String bpOpName = semanticRoot.generateUnusedName("__DebuggerExpr__%s");
		final String params = paramNames.size() > 0 ? "(" + String.join(", ", paramNames) + ")" : "";
		final String bpOpDef = bpOpName + params;		
		
		final String wrapper = "---- MODULE %s ----\nEXTENDS %s\n%s\n%s == %s\n====";
		String wrappedConditionExpr = String.format(wrapper, bpModName, rootModName, letExpr, bpOpDef, conditionExpr);
		byte[] wrappedConditionExprBytes = wrappedConditionExpr.getBytes(StandardCharsets.UTF_8);
		TLAplusParser parser = new TLAplusParser(new SilentSanyOutput(), wrappedConditionExprBytes);
		boolean syntaxParseSuccess = parser.parse();
		SyntaxTreeNode syntaxRoot = parser.ParseTree;
		if (!syntaxParseSuccess || null == syntaxRoot) {
			throw new ParseException("Syntax error while parsing breakpoint expression \"" + conditionExpr + "\"");
		}
		
		final Errors semanticLog = new Errors();
		final ExternalModuleTable emt = processor.getModuleTbl();
		// Resolve dependencies not already resolved.
		resolveDependencies(processor, emt, Stream.of(parser.dependencies())
				.filter(dep -> emt.getModuleNode(dep) == null).collect(Collectors.toList()), semanticLog);

		Generator semanticChecker = new Generator(emt, semanticLog);
		ModuleNode bpModule = semanticChecker.generate(syntaxRoot);
		if (null == bpModule || semanticLog.isFailure()) {
			throw new SemanticException(semanticLog.addMessage(ErrorCode.GENERAL, location,
					"Semantic error while parsing breakpoint expression \"%s\"", conditionExpr));
		}

		// Run level-checking. The operator should be restricted to
		// action-level or below.
		Errors levelCheckingErrors = new Errors();
		boolean levelCheckingSuccess = bpModule.levelCheck(levelCheckingErrors);
		if (!levelCheckingSuccess || levelCheckingErrors.isFailure() || !bpModule.levelCorrect) {
			throw new SemanticException(levelCheckingErrors.addMessage(ErrorCode.GENERAL, location,
					"Level-checking error while parsing breakpoint expression \"%s\"", conditionExpr));
		}
		
		bpOp = bpModule.getOpDef(bpOpName);
		if (null == bpOp) {
			throw new SemanticException(
					semanticLog.addMessage(ErrorCode.GENERAL, location,
							"Unable to find debugger expression op %s", bpOpName));
		}

		if (!(LevelConstants.ConstantLevel == bpOp.getLevel() || LevelConstants.VariableLevel == bpOp.getLevel()
				|| LevelConstants.ActionLevel == bpOp.getLevel())) {
			throw new SemanticException(semanticLog.addMessage(ErrorCode.OPERATOR_LEVEL_CONSTRAINTS_EXCEEDED, location,
					"Debug expressions must be action-level or below; actual level: %s",
					SemanticNode.levelToString(bpOp.getLevel())));
		}

		processor.processConstantsDynamicExtendee(bpModule);
		
		processor.processModuleOverrides(bpModule, emt);

		// See above for explanation. This can only be done after the module has been
		// fully processed (parsed, ...).
		for (OpDefNode def : letDefs) {
			bpModule.substituteFor(def, bpModule.getOpDef(def.getName()));
		}
		
		return bpOp;
	}
	
	private static ExternalModuleTable resolveDependencies(final SpecProcessor processor, final ExternalModuleTable emt,
			final List<String> dependencies, final Errors log) throws AbortException, ParseException, SemanticException {
		for (String moduleName : dependencies) {
			try (final InputStream moduleSource = new FileInputStream(
					ToolIO.getDefaultResolver().resolve(moduleName + TLAConstants.Files.TLA_EXTENSION, false))) {
				final TLAplusParser parser = new TLAplusParser(new SilentSanyOutput(), moduleSource);

				boolean syntaxParseSuccess = parser.parse();
				SyntaxTreeNode syntaxRoot = parser.ParseTree;
				if (!syntaxParseSuccess || null == syntaxRoot) {
					throw new ParseException("Syntax error while parsing breakpoint expression's dependency \"" + moduleName + "\"");
				}

		        // Transitively resolve dependencies.
				for (String dep : parser.dependencies()) {
					if (emt.getModuleNode(dep) == null) {
						resolveDependencies(processor, emt, List.of(dep), log);
					}
				}

				final Generator semanticParser = new Generator(emt, log);
				final ModuleNode module = semanticParser.generate(parser.rootNode());
				if (log.isFailure()) {
					continue;
				}
				module.levelCheck(log);
				// Process module's constants like numerals, strings, ...
				processor.processConstantsDynamicExtendee(module);
				emt.put(UniqueString.of(moduleName), semanticParser.getSymbolTable().getExternalContext(), module);
			} catch (IOException e) {
				log.addMessage(ErrorCode.MODULE_FILE_CANNOT_BE_FOUND, Location.nullLoc,
						"IO error while reading module \"%s\": %s", moduleName, e.getMessage());
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

	private static Set<SymbolNode> getScopedSymbols(ModuleNode semanticRoot, final List<SemanticNode> path) {
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