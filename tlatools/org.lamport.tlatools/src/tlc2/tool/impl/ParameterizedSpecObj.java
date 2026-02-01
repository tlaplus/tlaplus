/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool.impl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import tla2sany.drivers.SemanticException;
import tla2sany.modanalyzer.ModulePointer;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.SanyOutput;
import tla2sany.parser.ParseException;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tlc2.debug.TLCDebuggerExpression;
import tlc2.output.EC;
import tlc2.tool.Action;
import tlc2.tool.Defns;
import tlc2.util.Context;
import tlc2.value.impl.StringValue;
import util.Assert;
import util.FilenameToStream;

public class ParameterizedSpecObj extends SpecObj {

	public static final String ACTION_CONSTRAINTS = "ACTION_CONSTRAINT";
	public static final String CONSTRAINTS = "CONSTRAINT";
	public static final String POST_CONDITIONS = "POST_CONDITIONS";
	public static final String INVARIANT = "INVARIANT";

	private final Spec spec;
	private final Map<String, Object> params;

	public ParameterizedSpecObj(final Spec spec, final FilenameToStream resolver, final Map<String, Object> params) {
		super(spec.rootFile, resolver);
		this.spec = spec;
		this.params = params;
	}

	@Override
	protected final ParseUnit findOrCreateParsedUnit(final String name, final Errors errors, final boolean firstCall, final SanyOutput out)
			throws AbortException {
		final ParseUnit pu = super.findOrCreateParsedUnit(name, errors, firstCall, out);
		if (firstCall && params.containsKey(POST_CONDITIONS)) {
			final ModulePointer rootModule = pu.getRootModule();
			
			@SuppressWarnings("unchecked")
			final List<PostCondition> pcs = (List<PostCondition>) params.get(POST_CONDITIONS);
			for (PostCondition pc : pcs) {
				rootModule.getRelatives().addExtendee(pc.module);
			}
		}
		if (firstCall && params.containsKey(INVARIANT)) {
			final ModulePointer rootModule = pu.getRootModule();
			
			@SuppressWarnings("unchecked")
			final List<InvariantTemplate> invs = (List<InvariantTemplate>) params.get(INVARIANT);
			for (InvariantTemplate inv : invs) {
				inv.getModules().forEach(rootModule.getRelatives()::addExtendee);
			}
		}
		// TODO: The current approach forcefully extends the root module with the constraints’
		// modules. This should be replaced with infrastructure similar to
		// tlc2.debug.TLCDebuggerExpression.process(SpecProcessor, ModuleNode, Location, String),
		// which allows the root module’s extendees to remain unchanged. The existing approach
		// pollutes the module namespace and may introduce cyclic module dependencies.
		if (firstCall && params.containsKey(CONSTRAINTS)) {
			final ModulePointer rootModule = pu.getRootModule();

			@SuppressWarnings("unchecked")
			final List<Constraint> constraints = (List<Constraint>) params.get(CONSTRAINTS);
			for (Constraint c : constraints) {
				rootModule.getRelatives().addExtendee(c.module);
			}
		}
		if (firstCall && params.containsKey(ACTION_CONSTRAINTS)) {
			final ModulePointer rootModule = pu.getRootModule();

			@SuppressWarnings("unchecked")
			final List<Constraint> constraints = (List<Constraint>) params.get(ACTION_CONSTRAINTS);
			for (Constraint c : constraints) {
				rootModule.getRelatives().addExtendee(c.module);
			}
		}
		return pu;
	}

	@Override
	public void processConstantDefns(final Defns defns) {
		final ExternalModuleTable mt = getExternalModuleTable();

		// Process constants for CONSTRAINT
		@SuppressWarnings("unchecked")
		final List<Constraint> constraints = (List<Constraint>) params.getOrDefault(CONSTRAINTS, new ArrayList<>());
		for (final Constraint c : constraints) {
			processConstantsForModule(mt, c.module, c.constDefs, defns);
		}

		// Process constants for ACTION_CONSTRAINT
		@SuppressWarnings("unchecked")
		final List<Constraint> actionConstraints = (List<Constraint>) params.getOrDefault(ACTION_CONSTRAINTS,
				new ArrayList<>());
		for (final Constraint c : actionConstraints) {
			processConstantsForModule(mt, c.module, c.constDefs, defns);
		}

		// Process constants for POST_CONDITIONS
		@SuppressWarnings("unchecked")
		final List<PostCondition> postConditions = (List<PostCondition>) params.getOrDefault(POST_CONDITIONS,
				new ArrayList<>());
		for (final PostCondition pc : postConditions) {
			processConstantsForModule(mt, pc.module, pc.constDecls, defns);
		}

		// Process constants for INVARIANT
		// Note: InvariantTemplate doesn't currently have constant definitions,
		// but we check the modules in case they contain constants that need processing
		@SuppressWarnings("unchecked")
		final List<InvariantTemplate> invariants = (List<InvariantTemplate>) params.getOrDefault(INVARIANT,
				new ArrayList<>());
		for (final InvariantTemplate inv : invariants) {
			for (final String module : inv.getModules()) {
				processConstantsForModule(mt, module, new HashMap<>(), defns);
			}
		}

		super.processConstantDefns(defns);
	}

	private void processConstantsForModule(final ExternalModuleTable mt, final String moduleName,
			final Map<String, String> constDefs, final Defns defns) {
		final ModuleNode moduleNode = mt.getModuleNode(moduleName);
		Assert.check(moduleNode != null, EC.GENERAL, "Could not find module: " + moduleName);

		// Set the values of the constants used in the module
		final OpDeclNode[] constantDecls = moduleNode.getConstantDecls();
		for (int i = 0; i < constantDecls.length; i++) {
			final String constName = constantDecls[i].getName().toString();
			if (constDefs.containsKey(constName)) {
				final StringValue val = new StringValue(constDefs.get(constName));
				constantDecls[i].setToolObject(spec.getId(), val);
				defns.put(constName, val);
			}
		}
	}

	@Override
	public List<ExprNode> getPostConditionSpecs() {
		final List<ExprNode> res = new ArrayList<>();

		@SuppressWarnings("unchecked")
		final List<PostCondition> pcs = (List<PostCondition>) params.getOrDefault(POST_CONDITIONS, new ArrayList<>());
		for (PostCondition pc : pcs) {
			
			final ExternalModuleTable mt = getExternalModuleTable();
			final ModuleNode moduleNode = mt.getModuleNode(pc.module);
			Assert.check(moduleNode != null, EC.GENERAL, "Could not find module: " + pc.module);
			final OpDefNode opDef = moduleNode.getOpDef(pc.operator);
			Assert.check(opDef != null, EC.GENERAL,
					"Could not find operator: " + pc.operator + " in module: " + pc.module);
			res.add(opDef.getBody());
		}
		return res;
	}
	
	public static class PostCondition {
		public final String module;
		public final String operator;
		public final Map<String, String> constDecls;
		
		public PostCondition(String module, String operator) {
			this(module, operator, new HashMap<>());
		}
		
		public PostCondition(final String module, final String operator, final String def, final String constDef) {
			this(module, operator);
			this.constDecls.put(def, constDef);
		}

		public PostCondition(String module, String operator, Map<String, String> constDecls) {
			super();
			this.module = module;
			this.operator = operator;
			this.constDecls = constDecls;
		}
	}

	public static abstract class InvariantTemplate {

		protected final Set<String> modules;
		
		public InvariantTemplate(final Set<String> modules) {
			this.modules = modules;
		}
		
		public abstract Action getAction(final SpecProcessor spec) throws ParseException, SemanticException, AbortException;

		public Set<String> getModules() {
			// TODO:
			// CompileTimeInvariantTemplate: Returns the single module where the invariant
			// is both declared and defined.
			// RuntimeInvariantTemplate: Returns the set of modules that the invariant
			// depends on. The module where the invariant is declared and defined is managed
			// separately by TLCDebuggerExpression.
			return modules;
		}
	}	
	
	public static class RuntimeInvariantTemplate extends InvariantTemplate {
		private final String expr;

		public RuntimeInvariantTemplate(final Set<String> modules, final String expr) {
			super(modules);
			this.expr = expr;
		}

		@Override
		public Action getAction(final SpecProcessor spec) throws ParseException, SemanticException, AbortException {
			final OpDefNode opDef = TLCDebuggerExpression.process(spec, spec.getRootModule(), expr);
			return new Action(opDef.getBody(), Context.Empty, opDef, false, true);
		}
	}

	@Override
	public List<Action> getInvariants(final SpecProcessor specProcessor) throws ParseException, SemanticException, AbortException {
		final List<Action> res = new ArrayList<>();

		@SuppressWarnings("unchecked")
		final List<InvariantTemplate> invs = (List<InvariantTemplate>) params.getOrDefault(INVARIANT, new ArrayList<>());
		for (InvariantTemplate inv : invs) {
			res.add(inv.getAction(specProcessor));
		}
		return res;
	}

	public static class Constraint {

		private final String module;
		private final String operator;
		private final Map<String, String> constDefs;

		public Constraint(final String module, final String operator, final String def, final String constDef) {
			this(module, operator, Map.of(def, constDef));
		}

		public Constraint(final String module, final String operator, Map<String, String> constDefs) {
			this.module = module;
			this.operator = operator;
			this.constDefs = constDefs;
		}
	}

	@Override
	public List<OpDefNode> getConstraints() {
		@SuppressWarnings("unchecked")
		final List<OpDefNode> res = getConstraints0(
				(List<Constraint>) params.getOrDefault(CONSTRAINTS, new ArrayList<>()));
		return res;
	}

	@Override
	public List<OpDefNode> getActionConstraints() {
		@SuppressWarnings("unchecked")
		final List<OpDefNode> res = getConstraints0(
				(List<Constraint>) params.getOrDefault(ACTION_CONSTRAINTS, new ArrayList<>()));
		return res;
	}

	private List<OpDefNode> getConstraints0(final List<Constraint> constraints) {
		final List<OpDefNode> res = new ArrayList<>();
		final ExternalModuleTable mt = getExternalModuleTable();

		for (Constraint c : constraints) {
			final ModuleNode moduleNode = mt.getModuleNode(c.module);
			Assert.check(moduleNode != null, EC.GENERAL, "Could not find module: " + c.module);
			final OpDefNode opDef = moduleNode.getOpDef(c.operator);
			Assert.check(opDef != null, EC.GENERAL,
					"Could not find operator: " + c.operator + " in module: " + c.module);
			res.add(opDef);
		}
		return res;
	}

	public String getPostConditionRedefinition(final String key) {
		@SuppressWarnings("unchecked")
		final List<PostCondition> pcs = (List<PostCondition>) params.getOrDefault(POST_CONDITIONS, List.of());
		  	return pcs.stream()
  					.map(pc -> pc.redefinitions.get(key))
  					.filter(Objects::nonNull)
  					.findFirst()
  					.orElse(null);
  	}
}
