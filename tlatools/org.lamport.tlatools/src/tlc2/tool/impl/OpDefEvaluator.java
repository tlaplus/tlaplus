package tlc2.tool.impl;

import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.Enumerable.Ordering;

public interface OpDefEvaluator {
	IValue eval(SemanticNode body, Context c, TLCState s, CostModel doNotRecord);
	
	ContextEnumerator contexts(Ordering ordering, OpApplNode appl, Context c, TLCState s0, TLCState s1, final int control,
			CostModel cm);

	default ContextEnumerator contexts(OpApplNode appl, Context c) {
		return contexts(Ordering.UNDEFINED, appl, c, TLCState.Empty, TLCState.Empty, EvalControl.Const, CostModel.DO_NOT_RECORD);
	}
}
