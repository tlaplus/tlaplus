// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:19:03 PST by lamport
//      modified on Thu Dec  7 13:47:27 PST 2000 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.UserObj;
import tlc2.value.UserValue;
import tlc2.value.Value;

public class AnySet extends UserObj
{

    private static Value AnySet = new UserValue(new AnySet());

    public static Value ANY()
    {
        return AnySet;
    }

    public final int compareTo(Value val)
    {
        throw new EvalException(EC.TLC_MODULE_COMPARE_VALUE, new String[] { "ANY", Value.ppr(val.toString()) });
    }

    public final boolean member(Value val)
    {
        return true;
    }

    public final boolean isFinite()
    {
        return false;
    }

    public final StringBuffer toString(StringBuffer sb, int offset)
    {
        return sb.append("ANY");
    }
}
