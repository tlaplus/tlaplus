package tlc2.tool.impl;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.IValue;

public interface OpDefEvaluator {
	IValue eval(SemanticNode body, Context empty, TLCState empty2, CostModel doNotRecord);
}
