// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:15 PST by lamport
//      modified on Sat Jul 28 00:37:08 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.ExprNode;
import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Context;
import tlc2.value.BoolValue;
import tlc2.value.Value;
import util.Assert;
/**
 * Handles states
 * @author Leslie Lamport, Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
class LNStateAST extends LNState
{
    protected ExprNode body;

    public LNStateAST(ExprNode body, Context con)
    {
        super(con);
        this.body = body;
    }

    public final ExprNode getBody()
    {
        return this.body;
    }

    public final boolean eval(Tool tool, TLCState s1, TLCState s2)
    {
        Value val = tool.eval(this.body, con, s1);
        if (!(val instanceof BoolValue))
        {
            Assert.fail(EC.TLC_LIVE_STATE_PREDICATE_NON_BOOL);
        }
        return ((BoolValue) val).val;
    }

    public final void toString(StringBuffer sb, String padding)
    {
        sb.append(this.body);
    }
}
