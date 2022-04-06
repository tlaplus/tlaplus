/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package tlc2.tool.coverage;

import static tlc2.tool.ToolGlobals.OPCODE_unchanged;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.ITool;
import tlc2.tool.coverage.ActionWrapper.Relation;
import tlc2.util.Context;
import tlc2.util.ObjLongTable;
import tlc2.util.Vect;

/**
 * <h1>Why a CostModel:</h1> Why a CostModelCreator to traverses the semantic
 * graph to create a forest of OpApplNode trees (rooted at an action)?<br>
 * The semantic graph is no fit to store cost metrics. This is due to the fact
 * that the semantic graph has only a single node for each OpDefNode and thus
 * OpApplNode even when an OpApplNode is invoked from different actions and thus
 * different call trees. If we were to store costs inside the semantic graph, it
 * would thus not be possible to show costs per action. Therefore,
 * CostModelCreate creates a tree for each action whose subtree is the set of
 * OpApplNodes reachable from this particular action.
 * <p>
 * A CostModel tree of an action gets traversed by Tool in lockstep (except that
 * the tree only contains OpApplNodes thus <code>return this</code> in
 * OpApplNodeWrapper#get) when Tool traverses the semantic graph to evaluate an
 * action.
 * <p>
 * As part of the work on the CostModel, the ExplorerVisitor received an extension
 * to export the semantic graph into dot notation, which can be rendered with
 * GraphViz:
 * <code>java -cp tla2tools.jartla2sany.SANY -d ATLA+Spec.tla dot</code> It
 * optionally includes line numbers if the system property
 * <code>tla2sany.explorer.DotExplorerVisitor.includeLineNumbers=true</code>
 * is set.
 * <p>
 * -----------------------------------------------------------------------------
 * <h2>Note on performance:</h2> Spec/Tool and Value turn isCoverageEnabled into
 * constants. This should help the runtime to optimize away most calls to
 * CostModel unless coverage is enabled.
 * <p>
 * Macro-benchmarks on a real-world PlusCal [1] model show a 2% performance drop
 * in terms of throughput due to the addition of the "if (coverage) {...}" calls
 * when coverage is turned off (it is in the range of %40 when turned on). In
 * other words, the CostModel data collector has a non-zero overhead. The
 * reasons are unknown and further investigations have been abandoned. Instead,
 * the problem has been side-stepped by refactorings in ModelChecker and Tool.
 * [1]
 * https://bitbucket.org/parvmor/tarjanconcurrentscc/src/unionfind/specifications/MCBloemenSCC.tla
 * altered to terminate TLC after five minutes with TLCSet("exit",...)
 * <p>
 * The refactorings essentially decomposed large methods into smaller ones (see
 * git history for commits). This allows the runtime to emit more efficient code
 * s.t. hot methods can be inlined to reduce invocations. The net gain is in the
 * range of 5%; enough to make up for the 2% drop introduced by the CostModel
 * collector.<br>
 * Methods were identified by:
 * <code>java -XX:+PrintCompilation -XX:+UnlockDiagnosticVMOptions -XX:+PrintInlining
 * -jar tla2tools.jar -workers 1 | grep "hot method too big"</code>
 * <p>
 * A far more elegant implementation and zero-overhead solution of the CostModel
 * collector uses aspect-programming (based on e.g. AspectJ used in other places
 * of TLC). This approach has been prototyped in CostModelAspect.java. The
 * aspects in CostModelAspect are woven into TLC by AspectJ at the defined
 * pointcuts when needed.<br>
 * Weaving can either be done at compile-time (CTW) or launch-time (LTW) where
 * LTW is preferable in our case to only load the CostModel code when a user
 * enables it. Unfortunately, benchmarks revealed a huge performance drops in
 * the order of a magnitude with LTW. Inspections of the generated bytecode with
 * JitWatch did not reveal the root cause for this major performance drop. As a
 * side-effect, LTW would require TLC to include the AspectJ runtime - and even
 * bigger in size - the ASM bytecode instrumentation. Users would also have to
 * pass the -javaagent parameter to TLC. In other words, using coverage wouldn't
 * be as transparent to the user as it is today.
 * <p>
 * Experiments with CTW - compared to LTW - resulted in much better performance
 * with coverage enabled. Still, the overhead of CTW with coverage disabled was
 * non-negligible. We therefore went as far as hacking the class-loading in
 * TLC.java to load vanilla TLC with coverage off and instrumented code with
 * coverage on. However, we considered this approach to be too hack-ish and
 * abandoned it in favor of the aforementioned refactorings (it also broke the
 * model.ModelInJarfeature). It additionally increased the size of tla2tools.jar
 * two-fold.<br>
 * Generally it appears as if the code generation in AspectJ is not optimized to
 * emit the most efficient code. Most pointcuts result in superfluous object
 * allocations inside the generated bytecode - to pass along method parameters -
 * for *every* method invocation. Future versions of AspectJ might produce more
 * efficient code though.
 * <p>
 * -----------------------------------------------------------------------------
 * Changing tla2sany.semantic.Generator to generate a forest of call trees -
 * s.t. there is one OpDefNode & OpApplNode instance per call tree instead of
 * one global graph - appears to be the implementation with minimal overhead. We
 * did not follow up on this idea however, because of the inherent risk of
 * introducing subtle side-effect into the semantics of TLA+ expression
 * evaluation. An optimization - to only generate a forest when coverage is
 * enabled - that uses dynamic proxies (JDK dynamic proxies, CGLib, ASM) proved
 * impossible unless the complete class hierarchy of SemanticNode gets
 * refactored into a hierarchy with interfaces (proxies can practically only be
 * generated for interfaces)
 */
public class CostModelCreator extends ExplorerVisitor {

	private final Deque<CostModelNode> stack = new ArrayDeque<>();
	private final Map<ExprOrOpArgNode, Subst> substs = new HashMap<>();
	private final Map<OpApplNode, Set<OpApplNodeWrapper>> node2Wrapper = new HashMap<>();
	private final Set<OpDefNode> opDefNodes = new HashSet<>();
	// Set of OpDefNodes occurring in LetIns and their OpApplNodes.
	private final Map<ExprNode, ExprNode> letIns = new HashMap<>();
	// OpAppNode does not implement equals/hashCode which causes problem when added
	// to sets or maps. E.g. for a test, an OpApplNode instance belonging to
	// Sequences.tla showed up in coverage output.
	private final Set<OpApplNodeWrapper> nodes = new HashSet<>();
	private final ITool tool;
	
	private ActionWrapper root;
	private Context ctx = Context.Empty;
	
	private CostModelCreator(final SemanticNode root, final ITool tool) {
		this.tool = tool;
		this.stack.push(new RecursiveOpApplNodeWrapper());
		root.walkGraph(new CoverageHashTable(opDefNodes), this);
	}

	// root cannot be type OpApplNode but has to be SemanticNode (see Test216).
	private CostModelCreator(final ITool tool) {
		this.tool = tool;
		// MAK 10/08/2018: Annotate OApplNodes in the semantic tree that correspond to
		// primed vars. It is unclear why OpApplNodes do not get marked as primed when
		// instantiated. The logic in Tool#getPrimedLocs is too obscure to tell.
		final ObjLongTable<SemanticNode>.Enumerator<SemanticNode> keys = tool.getPrimedLocs().keys();
		SemanticNode sn;
		while ((sn = keys.nextElement()) != null) {
			this.nodes.add(new OpApplNodeWrapper((OpApplNode) sn, null));
		}
	}

	private CostModel getCM(final Action act, final ActionWrapper.Relation relation) {
		this.substs.clear();
		this.node2Wrapper.clear();
		this.opDefNodes.clear();
		this.letIns.clear();
		this.stack.clear();
		this.ctx = Context.Empty;
		
		this.root = new ActionWrapper(act, relation);
		this.stack.push(root);
		act.pred.walkGraph(new CoverageHashTable(opDefNodes), this);
		
		assert this.stack.peek().isRoot();
		return this.stack.peek().getRoot();
	}

	@Override
	public void preVisit(final ExploreNode exploreNode) {
		if (exploreNode instanceof OpApplNode) {
			final OpApplNode opApplNode = (OpApplNode) exploreNode;
			if (opApplNode.isStandardModule()) {
				return;
			}
			
	        final OpApplNodeWrapper oan;
			if (opApplNode.hasOpcode(OPCODE_unchanged)) {
				oan = new UnchangedOpApplNodeWrapper(opApplNode, this.root);
			} else {
				oan = new OpApplNodeWrapper(opApplNode, this.root);
			}
			
			if (nodes.contains(oan)) {
				oan.setPrimed();
			}
			
			// A (recursive) function definition nested in LetIn:
			//   LET F[n \in S] == e
			//   IN F[...]
			// with e either built from F or not.
			if (letIns.containsKey(opApplNode)) {
				// At the visit of the LETIN node in the walk over the semantic graph we stored
				// the mapping from the LET part to the IN part in this.lets (see LetInNode below).
				// Here, we add the LET parts(s) to the lets of the IN part if it is found on
				// the stack (this is more involved because we have to find the OANWrappers and
				// not just the OANs). 
				final ExprNode in = letIns.get(opApplNode);
				for (CostModelNode cmn : stack) {
					final SemanticNode node = cmn.getNode();
					if (node == in && cmn instanceof OpApplNodeWrapper) {
						// addLets instead of addChild because lets can be added multiple times
						// whereas addChild asserts a child to be added only once.
						((OpApplNodeWrapper) cmn).addLets(oan);
					}
				}
			}
			
			// CONSTANT operators (including definition overrides...)
			final SymbolNode operator = opApplNode.getOperator();
			final Object val = tool.lookup(operator);
			if (val instanceof OpDefNode && operator != val) { // second conjunct bc lookup returns operator when nothing else found.
				final OpDefNode odn = (OpDefNode) val;
				final ExprNode body = odn.getBody();
				if (body instanceof OpApplNode) {
					final CostModelCreator substitution = new CostModelCreator(body, tool);
					oan.addChild((OpApplNodeWrapper) substitution.getModel());
				}
			}			
			
			// RECURSIVE
			if (operator instanceof OpDefNode) {
				final OpDefNode odn = (OpDefNode) operator;
				if (odn.getInRecursive()) {
					stack.stream()
							.filter(w -> w.getNode() != null && w.getNode() instanceof OpApplNode
									&& ((OpApplNode) w.getNode()).getOperator() == odn)
							.findFirst().ifPresent(cmn -> oan.setRecursive(cmn));
				}
			}

			// Higher-order operators/Operators as arguments (LAMBDA, ...)
			//
			// line X: Foo(Op(_), S) == \A s \in S: Op(s)
			// line ?: ...
			// line Y: Bar == Foo(LAMBDA e: e..., {1,2,3})
			//
			// This is the most involved part of CMC: The task is to make the OANW
			// corresponding to the RHS of the LAMBDA expression on line Y a child of Op(s)
			// on line X. However, the graph exploration is DFS which means that we haven't
			// seen the LAMBDA on line Y when we are at the Op(s) on line X and we've
			// (mostly) forgotten about Op(s) when we see the LAMBDA. ToolImpl - as part of
			// its DFS over the semantic graph - passes a context along which gets extended
			// or *branched*. Here, we cannot pass a Context along the decent but instead
			// keep a single, global context. 
			//
			// The global context does not create a problem with regards to correctness, but
			// can lead to long context chains for larger specifications. Therefore, only
			// extend the context when opApplNode.argsContainOpArgNodes() is true, i.e. when
			// one or more arguments of an operator are also operators (such as a LAMBDA).
			// Without this safeguard, the time to create the CostModel for the SchedMono
			// specification took approximately 60 seconds. With the safeguard, it is down
			// to a second or two.
			//
			// To summarize, this is a clutch that has been hacked to be good enough!
			// 
			// if-branches 1., 2., and 3. below are evaluated in three distinct
			// invocation of outer preVisit for different ExploreNodes.
			if (tool != null && operator instanceof OpDefNode && opApplNode.hasOpcode(0)
					&& opApplNode.argsContainOpArgNodes()) {
				// 1) Maintain Context for all OpApplNode iff one or more of its args are of
				// type OpArgNode. This is more restrictive than Tool.
				final OpDefNode odn = (OpDefNode) operator;
				if (odn.hasOpcode(0) && !odn.isStandardModule()) {
					this.ctx = tool.getOpContext(odn, opApplNode.getArgs(), ctx, false);
				}
			}
			final Object lookup = this.ctx.lookup(opApplNode.getOperator());
			if (lookup instanceof OpDefNode) {
				// 2) Context has an entry for the given body where body is 'LAMBDA e: e...' and
				// oan is 'Op(s)'. Remember for later.
				final ExprNode body = ((OpDefNode) lookup).getBody();
				if (body instanceof OpApplNode) {
					// Design choice:
					// Might as well store the mapping from body to oan via
					// body#setToolObject(tla2sany.semantic.FrontEnd.getToolId(), oan) instead of in
					// node2Wrapper. However, node2Wrapper can be gc'ed after the CostModel has been
					// created and before state space exploration.
					this.node2Wrapper.computeIfAbsent((OpApplNode) body, key -> new HashSet<>()).add(oan);
				}
			}
			if (this.node2Wrapper.containsKey(opApplNode)) {
				// 3) Now it's later. Connect w and oan where
				// w is 'Op(s)' and oan is 'LAMBDA e: e...'
				this.node2Wrapper.get(opApplNode).forEach(w -> w.addChild(oan));
			}
			// End of Higher-order operators/Operators as arguments (LAMBDA, ...) 
			
			// Substitutions
			if (this.substs.containsKey(exploreNode)) {
				final Subst subst = this.substs.get(exploreNode);
				assert subst.getExpr() == oan.getNode();
				subst.setCM(oan);
			}
			
			final CostModelNode parent = stack.peek();
			parent.addChild(oan.setLevel(parent.getLevel() + 1));
			stack.push(oan);
		} else if (exploreNode instanceof SubstInNode) {
			final SubstInNode sin = (SubstInNode) exploreNode;
			final Subst[] substs = sin.getSubsts();
			for (Subst subst : substs) {
				this.substs.put(subst.getExpr(), subst);
			}
		} else if (exploreNode instanceof LetInNode) {
			final LetInNode lin = (LetInNode) exploreNode;
			for (OpDefNode opDefNode : lin.getLets()) {
				letIns.put(opDefNode.getBody(), lin.getBody());
			}
		} else if (exploreNode instanceof OpDefNode) {
			//TODO Might suffice to just keep RECURSIVE ones.
			opDefNodes.add((OpDefNode) exploreNode);
		}
	}

	@Override
	public void postVisit(final ExploreNode exploreNode) {
		if (exploreNode instanceof OpApplNode) {
			if (((OpApplNode) exploreNode).isStandardModule()) {
				return;
			}
			final CostModelNode pop = stack.pop();
			assert pop.getNode() == exploreNode;
		} else if (exploreNode instanceof OpDefNode) {
			final boolean removed = opDefNodes.remove((OpDefNode) exploreNode);
			assert removed;
		}
	}

	private CostModel getModel() {
		assert this.stack.peek().isRoot();
		return this.stack.peek().getRoot();
	}
	
	public static final void create(final ITool tool) {
		final CostModelCreator collector = new CostModelCreator(tool);

		// TODO Start from the ModuleNode similar to how the Explorer works. It is
		// unclear how to lookup the corresponding subtree in the global CM graph
		// in getNextState and getInitStates of the model checker.
		final Vect<Action> init = tool.getInitStateSpec();
		for (int i = 0; i < init.size(); i++) {
			final Action initAction = init.elementAt(i);
			initAction.cm = collector.getCM(initAction, Relation.INIT);
		}

		final Map<SemanticNode, CostModel> cms = new HashMap<>();
		for (Action nextAction : tool.getActions()) {
			if (cms.containsKey(nextAction.pred)) {
				nextAction.cm = cms.get(nextAction.pred);
			} else {
				nextAction.cm = collector.getCM(nextAction, Relation.NEXT);
				cms.put(nextAction.pred, nextAction.cm);
			}
		}

		for (Action invariant : tool.getInvariants()) {
			if (!invariant.isInternal()) {
				invariant.cm = collector.getCM(invariant, Relation.PROP);
			}
		}
		
		// action constraints
		final ExprNode[] actionConstraints = tool.getActionConstraints();
		for (ExprNode exprNode : actionConstraints) {
			final OpDefNode odn = (OpDefNode) exprNode.getToolObject(tool.getId());
			final Action act = new Action(exprNode, Context.Empty, odn);
			act.cm = collector.getCM(act, Relation.CONSTRAINT);
			exprNode.setToolObject(tool.getId(), act);
		}
		// state constraints
		final ExprNode[] modelConstraints = tool.getModelConstraints();
		for (ExprNode exprNode : modelConstraints) {
			final OpDefNode odn = (OpDefNode) exprNode.getToolObject(tool.getId());
			final Action act = new Action(exprNode, Context.Empty, odn);
			act.cm = collector.getCM(act, Relation.CONSTRAINT);
			exprNode.setToolObject(tool.getId(), act);
		}
		
        // https://github.com/tlaplus/tlaplus/issues/413#issuecomment-577304602
        if (Boolean.getBoolean(CostModelCreator.class.getName() + ".implied")) {
    		for (Action impliedInits : tool.getImpliedInits()) {
    			impliedInits.cm = collector.getCM(impliedInits, Relation.PROP);
    		}
    		for (Action impliedActions : tool.getImpliedActions()) {
    			impliedActions.cm = collector.getCM(impliedActions, Relation.PROP);
    		}
        }
	}
	
	public static void report(final ITool tool, final long startTime) {
        MP.printMessage(EC.TLC_COVERAGE_START);
    	final Vect<Action> init = tool.getInitStateSpec();
    	for (int i = 0; i < init.size(); i++) {
    		final Action initAction = init.elementAt(i);
    		initAction.cm.report();
    	}

		// Order next-state actions based on location to print in order of location.
		// Note that Action[] actions may contain action instances with identical
		// location which is the case for actions that are evaluated in the scope of a
		// Context, i.e. \E s \in ProcSet: action(s) \/ ...
    	// However, actions with identical location share the ActionWrapper instance
    	// which is why we can non-deterministically choose to report one of it without
    	// producing bogus results (see CostModelCreator.preVisit(ExploreNode) above).
    	final Action[] actions = tool.getActions();
        final Set<CostModel> reported = new HashSet<>();
        final Set<Action> sortedActions = new TreeSet<>(new Comparator<Action>() {
			@Override
			public int compare(Action o1, Action o2) {
				return o1.pred.getLocation().compareTo(o2.pred.getLocation());
			}
		});
        sortedActions.addAll(Arrays.asList(actions));
        for (Action action : sortedActions) {
        	if (!reported.contains(action.cm)) {
        		action.cm.report();
        		reported.add(action.cm);
        	}
		}
        
        for (Action invariant : tool.getInvariants()) {
			if (!invariant.isInternal()) {
	        	//TODO May need to be ordered similar to next-state actions above.
	        	invariant.cm.report();
			}
		}
        
		// action constraints
		final ExprNode[] actionConstraints = tool.getActionConstraints();
		for (ExprNode exprNode : actionConstraints) {
			final Action act = (Action) exprNode.getToolObject(tool.getId());
			act.cm.report();
		}
		// state constraints
		final ExprNode[] modelConstraints = tool.getModelConstraints();
		for (ExprNode exprNode : modelConstraints) {
			final Action act = (Action) exprNode.getToolObject(tool.getId());
			act.cm.report();
		}
        
        // https://github.com/tlaplus/tlaplus/issues/413#issuecomment-577304602
        if (Boolean.getBoolean(CostModelCreator.class.getName() + ".implied")) {
    		for (Action impliedInits : tool.getImpliedInits()) {
    			impliedInits.cm.report();
    		}
    		for (Action impliedActions : tool.getImpliedActions()) {
    			impliedActions.cm.report();
    		}
        }
       
		// Notify users about the performance overhead related to coverage collection
		// after N minutes of model checking. The assumption is that a user has little
		// interest in coverage for a large (long-running) model anyway.  In the future
        // it is hopefully possible to switch from profiling to sampling to relax the
        // performance overhead of coverage and cost statistics.
		final long l = System.currentTimeMillis() - startTime;
		if (l > (5L * 60L * 1000L)) {
			MP.printMessage(EC.TLC_COVERAGE_END_OVERHEAD);
		} else {
			MP.printMessage(EC.TLC_COVERAGE_END);
		}
	}
}
