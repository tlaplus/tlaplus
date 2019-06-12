// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:02 PST by lamport
//      modified on Fri Sep 22 13:18:45 PDT 2000 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.ExprOrOpArgNode;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;

public abstract class OpValue extends Value implements Applicable {

	// Allow sub-classes to override.
	public Value eval(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
			final TLCState s1, final int control, final CostModel cm) {
		final Value[] argVals = new Value[args.length];
		// evaluate the operator's arguments:
		for (int i = 0; i < args.length; i++) {
			argVals[i] = tool.eval(args[i], c, s0, s1, control, cm);
		}
		// evaluate the operator:
		return this.apply(argVals, control);
	}
}
