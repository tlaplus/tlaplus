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

import tla2sany.semantic.LetInNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SubstInNode;
import tla2sany.st.Location;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;

public final class ActionWrapper extends CostModelNode {

	public enum Relation {
		INIT, NEXT, PROP, CONSTRAINT;
	}
	
	private final Action action;
	private final Relation relation;
	
	public ActionWrapper(final Action action, Relation rel) {
		this.action = action;
		this.relation = rel;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.coverage.CostModelNode#getLocation()
	 */
	@Override
	protected Location getLocation() {
		if (this.action.isDeclared()) {
			return this.action.getDeclaration();
		}
		return this.action.pred.getLocation();
	}

	private String printLocation() {
		if (!this.action.isDeclared()) {
			// Safeguard for legacy cases if any.
			return this.action.toString();
		}
		// Determine if the mapping from the action's name/identifier/declaration to the
		// action's definition is 1:1 or 1:N.
		//
		// Act == /\ x  = 23
		//        /\ x' = 42
		// vs
		// Act == \/ /\ x  = 23
		//           /\ x' = 42
		//        \/ /\ x  = 123
		//           /\ x' = 4711
		// or
		// Act == (x  = 23 /\ x' = 42) \/ (x  = 123 /\ x' = 4711)
		//
		// For a 1:1 mapping this prints just the location of Act. For a 1:N mapping it
		// prints the location of Act _and_ the location (in shortened form) of the actual
		// disjunct.
		final Location declaration = this.action.getDeclaration();
		final Location definition = this.action.getOpDef().getBody().getLocation();
		final Location actual = this.action.pred.getLocation();
		if (definition.equals(actual)) {
			// 1:1
			return String.format("<%s %s>", this.action.getName(), declaration);
		} else {
			// 1:N
			return String.format("<%s %s (%s %s %s %s)>", this.action.getName(), declaration, actual.beginLine(),
					actual.beginColumn(), actual.endLine(), actual.endColumn());
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.coverage.CostModelNode#getRoot()
	 */
	@Override
	public CostModelNode getRoot() {
		return this;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.CostModel#get(tla2sany.semantic.SemanticNode)
	 */
	@Override
	public final CostModel get(final SemanticNode eon) {
		// returns this instance in case no match is found in children. As a result, the
		// CostModel will be incorrect which is not as severe as running into an NPE.
		if (eon instanceof SubstInNode) {
			final SubstInNode sin = (SubstInNode) eon;
			return this.children.getOrDefault(sin.getBody(), this);
		} else if (eon instanceof LetInNode) {
			final LetInNode lin = (LetInNode) eon;
			return this.children.getOrDefault(lin.getBody(), this);
		}
		return this.children.getOrDefault(eon, this);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.coverage.CostModelNode#getNode()
	 */
	@Override
	SemanticNode getNode() {
		return action.pred;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.coverage.CostModelNode#isRoot()
	 */
	@Override
	boolean isRoot() {
		return true;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.coverage.CostModel#report()
	 */
	public CostModel report() {
		// Report count for action itself.
		if (relation == Relation.PROP) {
			assert getEvalCount() == 0L && this.secondary.getCount() == 0L;
			MP.printMessage(EC.TLC_COVERAGE_PROPERTY, new String[] { printLocation() });
		} else if (relation == Relation.INIT) {
			// TODO Eventually coverage for init and next should consistently report states
			// found and distinct states into the same counters.
			MP.printMessage(EC.TLC_COVERAGE_INIT, new String[] { printLocation(), String.valueOf(getEvalCount()),
					String.valueOf(getEvalCount() + this.secondary.getCount()) });
		} else if (relation == Relation.CONSTRAINT) {
			MP.printMessage(EC.TLC_COVERAGE_CONSTRAINT,
					new String[] { printLocation(), String.valueOf(this.secondary.getCount()),
							String.valueOf(getEvalCount() + this.secondary.getCount()) });
		} else {
			MP.printMessage(EC.TLC_COVERAGE_NEXT, new String[] { printLocation(),
					String.valueOf(this.secondary.getCount()), String.valueOf(getEvalCount()) });
		}

		// An action has single child which is the OpApplNodeWrapper with the OpApplNode
		// for this OpDefNode unless the action's pred is a substitution or a let/in expr.
		assert !(this.action.pred instanceof SubstInNode || this.action.pred instanceof LetInNode)
				? this.children.size() == 1
				: !this.children.isEmpty();
		// Let children report.
		// Could disable here if decided to implement action-only coverage at the TLC
		// level (see org.lamport.tla.toolbox.tool.tlc.model.Model.Coverage).
		this.children.values().forEach(c -> c.report());
		return this;
	}

	public boolean is(Relation r) {
		return r == this.relation;
	}
}
