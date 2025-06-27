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

import tla2sany.modanalyzer.ModulePointer;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.SanyOutput;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.debug.TLCDebuggerExpression;
import tlc2.tool.Action;
import tlc2.util.Context;
import tlc2.value.impl.StringValue;
import util.FilenameToStream;

public class ParameterizedSpecObj extends SpecObj {

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

			for (Map.Entry<String, String> entry : pc.redefinitions.entrySet()) {
				final OpDefNode redefined = moduleNode.getOpDef(entry.getKey());
				redefined.setToolObject(spec.getId(), new StringValue(entry.getValue()));
			}

			res.add(opDef.getBody());
		}
		return res;
	}
	
	public static class PostCondition {
		public final String module;
		public final String operator;
		public final Map<String, String> redefinitions;

		public PostCondition(String moduleBangOp) {
			this(moduleBangOp.split("!")[0], moduleBangOp.split("!")[1]);
		}
		
		public PostCondition(String module, String operator) {
			this(module, operator, new HashMap<>());
		}
		
		public PostCondition(final String module, final String operator, final String def, final String redef) {
			this(module, operator);
			this.redefinitions.put(def, redef);
		}

		public PostCondition(String module, String operator, Map<String, String> redefinitions) {
			super();
			this.module = module;
			this.operator = operator;
			this.redefinitions = redefinitions;
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
	
	// Note: There is exactly one instance of CompileTimeInvariantTemplate, which is
	// specifically created for the TLA+ Debugger. Unfortunately, I couldn't find a
	// way to implement this using RuntimeInvariantTemplate—which would eliminate
	// the need for this separation—because it requires a Java module override.
	// The Java module override is matched and connected to its TLA+ counterpart
	// before the RuntimeInvariantTemplate is processed.  Thus, without the
	// CompileTimeInvariantTemplate, the connection between the Java module override
	// and its TLA+ counterpart would not be established.
	public static class CompileTimeInvariantTemplate extends InvariantTemplate {
		private final String operator;
		
		public CompileTimeInvariantTemplate(String module, String operator) {
			super(Set.of(module));
			this.operator = operator;
		}

		@Override
		public Action getAction(final SpecProcessor spec) {
			final ExternalModuleTable mt = spec.getModuleTbl();
			final ModuleNode moduleNode = mt.getModuleNode(modules.iterator().next());
			final OpDefNode opDef = moduleNode.getOpDef(operator);			
			return new Action(opDef.getBody(), Context.Empty, opDef, false, true);
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
}
