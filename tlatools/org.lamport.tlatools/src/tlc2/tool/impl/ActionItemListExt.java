/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved.
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

import tla2sany.semantic.SemanticNode;
import tlc2.tool.Action;
import tlc2.tool.IActionItemList;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;

public class ActionItemListExt extends ActionItemList {

	public final static ActionItemList Empty = new ActionItemListExt(null, null, 0, null, null);

	private ActionItemListExt prev;

	private Action action;

	protected ActionItemListExt(SemanticNode pred, Context con, int kind, ActionItemList next, CostModel cm) {
		super(pred, con, kind, next, cm);
	}

	@Override
	public IActionItemList cons(SemanticNode pred, Context con, CostModel cm, int kind) {
		ActionItemListExt actionItemListExt = new ActionItemListExt(pred, con, kind, this, coverage ? cm.get(pred) : cm);
		actionItemListExt.action = getAction();
		return actionItemListExt;
	}

	@Override
	public ActionItemList cons(final Action act, final int kind) {
		final ActionItemListExt actionItemListExt = new ActionItemListExt(act.pred, act.con, kind, this, coverage ? act.cm.get(pred) : act.cm);
		actionItemListExt.action = act;
		return actionItemListExt;
	}

	@Override
	public ActionItemList cdr() {
		final ActionItemListExt cdr = (ActionItemListExt) super.cdr();
		cdr.prev = this;
		return cdr;
	}

	@Override
	public boolean isEmpty() {
		return this == Empty;
	}

	@Override
	public void setAction(final Action action) {
		this.action = action;
	}

	@Override
	public Action getAction() {
		if (this.prev != null) {
			return this.prev.action;
		}
		return action;
	}
}
