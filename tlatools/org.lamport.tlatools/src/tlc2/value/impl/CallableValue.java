/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
package tlc2.value.impl;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.OpDefNode;
import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import util.Assert;

import java.lang.invoke.MethodHandles;
import java.lang.reflect.Method;
import java.util.concurrent.Callable;

public class CallableValue extends EvaluatingValue {

    private static final long serialVersionUID = 3406961825539255119L;

    public CallableValue(final Method md, final int minLevel, final OpDefNode opDef) throws IllegalAccessException {
        super(MethodHandles.publicLookup().unreflect(md).asSpreader(IValue[].class, md.getParameterCount()), md, minLevel, 100, opDef);
    }

    @Override
    public Value eval(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
                      final TLCState s1, final int control, final CostModel cm) {
        final Value[] argVals = new Value[args.length];
        // evaluate the operator's arguments:
        for (int i = 0; i < args.length; i++) {
            argVals[i] = tool.eval(args[i], c, s0, s1, control, cm);
        }
        try {
            final Callable<?> cl = (Callable<?>) this.mh.invoke((Object) argVals);
            s1.setCallable(cl);
        } catch (final Throwable e) {
            Assert.fail(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[]{this.md.toString(), e.getMessage()});
        }
        return BoolValue.ValTrue;
    }
}
