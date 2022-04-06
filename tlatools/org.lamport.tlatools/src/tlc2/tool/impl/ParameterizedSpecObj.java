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

import tla2sany.modanalyzer.ModulePointer;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
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
	protected final ParseUnit findOrCreateParsedUnit(final String name, final Errors errors, final boolean firstCall)
			throws AbortException {
		final ParseUnit pu = super.findOrCreateParsedUnit(name, errors, firstCall);
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
			final List<Invariant> invs = (List<Invariant>) params.get(INVARIANT);
			for (Invariant inv : invs) {
				rootModule.getRelatives().addExtendee(inv.module);
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

	public static class Invariant {
		public final String module;
		public final String operator;
		
		public Invariant(String module, String operator) {
			super();
			this.module = module;
			this.operator = operator;
		}
	}

	@Override
	public List<Action> getInvariants() {
		final List<Action> res = new ArrayList<>();

		@SuppressWarnings("unchecked")
		final List<Invariant> invs = (List<Invariant>) params.getOrDefault(INVARIANT, new ArrayList<>());
		for (Invariant inv : invs) {
			
			final ExternalModuleTable mt = getExternalModuleTable();
			final ModuleNode moduleNode = mt.getModuleNode(inv.module);
			final OpDefNode opDef = moduleNode.getOpDef(inv.operator);
			
			res.add(new Action(opDef.getBody(), Context.Empty, opDef, false, true));
		}
		return res;
	}
}
