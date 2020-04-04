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

import java.util.HashSet;
import java.util.Iterator;

import tla2sany.semantic.ExprNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.util.Context;
import tlc2.util.List;
import tlc2.value.impl.LazyValue;

public abstract class Specs {

	/** 
	 * The level of the expression according to level checking.
	 * static method, does not change instance state 
	 */
	public static int getLevel(LevelNode expr, Context c)
	{
	    HashSet<SymbolNode> lpSet = expr.getLevelParams();
	    if (lpSet.isEmpty())
	        return expr.getLevel();
	
	    int level = expr.getLevel();
	    Iterator<SymbolNode> iter = lpSet.iterator();
	    while (iter.hasNext())
	    {
	        SymbolNode param = (SymbolNode) iter.next();
	        Object res = c.lookup(param, true);
	        if (res != null)
	        {
	            if (res instanceof LazyValue)
	            {
	                LazyValue lv = (LazyValue) res;
	                int plevel = getLevel((LevelNode) lv.expr, lv.con);
	                level = (plevel > level) ? plevel : level;
	            } else if (res instanceof OpDefNode)
	            {
	                int plevel = getLevel((LevelNode) res, c);
	                level = (plevel > level) ? plevel : level;
	            }
	        }
	    }
	    return level;
	}

	/**
	 * Static method, does not change instance state
	 * @param expr
	 * @param subs
	 * @return
	 */
	public static final ExprNode addSubsts(ExprNode expr, List subs)
	{
	    ExprNode res = expr;
	
	    while (!subs.isEmpty())
	    {
	        SubstInNode sn = (SubstInNode) subs.car();
	        res = new SubstInNode(sn.stn, sn.getSubsts(), res, sn.getInstantiatingModule(), sn.getInstantiatedModule());
	        subs = subs.cdr();
	    }
	    return res;
	}
}