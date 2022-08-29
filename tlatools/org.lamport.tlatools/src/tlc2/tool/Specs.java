/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package tlc2.tool;

import tla2sany.semantic.*;
import tlc2.util.Context;
import tlc2.value.impl.LazyValue;

import java.util.HashSet;
import java.util.LinkedList;

public abstract class Specs {

    /**
     * The level of the expression according to level checking.
     * static method, does not change instance state
     */
    public static int getLevel(final LevelNode expr, final Context c) {
        final HashSet<SymbolNode> lpSet = expr.getLevelParams();
        if (lpSet.isEmpty())
            return expr.getLevel();

        int level = expr.getLevel();
        for (final SymbolNode param : lpSet) {
            final Object res = c.lookup(param, true);
            if (res != null) {
                if (res instanceof final LazyValue lv) {
                    final int plevel = getLevel((LevelNode) lv.expr, lv.con);
                    level = Math.max(plevel, level);
                } else if (res instanceof OpDefNode) {
                    final int plevel = getLevel((LevelNode) res, c);
                    level = Math.max(plevel, level);
                }
            }
        }
        return level;
    }

    /**
     * Static method, does not change instance state
     */
    public static ExprNode addSubsts(final ExprNode expr, final LinkedList<SubstInNode> subs) {
        ExprNode res = expr;


        for (final SubstInNode sn : subs) {
            res = new SubstInNode(sn.stn, sn.getSubsts(), res, sn.getInstantiatingModule(), sn.getInstantiatedModule());
        }
        return res;
    }
}