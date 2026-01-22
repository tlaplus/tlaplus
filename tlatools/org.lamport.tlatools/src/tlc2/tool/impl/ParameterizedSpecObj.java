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
import java.util.Set;
import java.util.stream.Stream;

import tla2sany.modanalyzer.ModulePointer;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.SanyOutput;
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
	public List<ExprNode> getPostConditionSpecs() {
		final List<ExprNode> res = new ArrayList<>();

		@SuppressWarnings("unchecked")
		final List<PostCondition> pcs = (List<PostCondition>) params.getOrDefault(POST_CONDITIONS, new ArrayList<>());
		for (PostCondition pc : pcs) {
			
			final ExternalModuleTable mt = getExternalModuleTable();
			final ModuleNode moduleNode = mt.getModuleNode(pc.module);
			final OpDefNode opDef = moduleNode.getOpDef(pc.operator);

			Stream.of(moduleNode.getConstantDecls()).forEach(decl -> decl.setToolObject(spec.getId(),
					new StringValue(pc.constDecls.get(decl.getName().toString()))));

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
		
		public abstract Action getAction(final SpecProcessor spec);

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

		public RuntimeInvariantTemplate(final String expr) {
			this(Set.of(), expr);
		}

		public RuntimeInvariantTemplate(final Set<String> modules, final String expr) {
			super(modules);
			this.expr = expr;
		}

		@Override
		public Action getAction(final SpecProcessor spec) {
			final OpDefNode opDef = TLCDebuggerExpression.process(spec, spec.getRootModule(), expr);
			return new Action(opDef.getBody(), Context.Empty, opDef, false, true);
		}
	}

	@Override
	public List<Action> getInvariants(final SpecProcessor specProcessor) {
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

		for (Constraint c : constraints) {
			final ExternalModuleTable mt = getExternalModuleTable();
			final ModuleNode moduleNode = mt.getModuleNode(c.module);
			Assert.check(moduleNode != null, EC.GENERAL, "Could not find module: " + c.module);

			// Set the values of the constant used in the constraint.
			final OpDeclNode[] constantDecls = moduleNode.getConstantDecls();
			for (int i = 0; i < constantDecls.length; i++) {
				final String constName = constantDecls[i].getName().toString();
				if (c.constDefs.containsKey(constName)) {
					constantDecls[i].setToolObject(spec.getId(), new StringValue(c.constDefs.get(constName)));
				}
			}

			final OpDefNode opDef = moduleNode.getOpDef(c.operator);
			Assert.check(opDef != null, EC.GENERAL,
					"Could not find operator: " + c.operator + " in module: " + c.module);
			res.add(opDef);
		}
		return res;
	}
}
