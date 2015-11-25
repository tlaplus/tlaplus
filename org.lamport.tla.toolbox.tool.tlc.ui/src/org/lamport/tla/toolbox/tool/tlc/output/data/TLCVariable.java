/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.output.data;

public class TLCVariable
{
    private String name;
    private TLCVariableValue value;
    private boolean isTraceExplorerVar;

    public TLCVariable(String name, TLCVariableValue value)
    {
        this.name = name;
        this.value = value;
        this.isTraceExplorerVar = false;

    }

    public String getName()
    {
        return name;
    }

    public TLCVariableValue getValue()
    {
        return value;
    }

    public String toString()
    {
        return value == null ? "" : value.toString();
    }

    public void setName(String name)
    {
        this.name = name;
    }

    public void setValue(TLCVariableValue value)
    {
        this.value = value;
    }

    /**
     * Returns whether or not this variable represents
     * a trace explorer expression. See {@link TLCVariable#setTraceExplorerVar(boolean)}
     * for setting the value returned by this method. By default, it is false.
     * @return
     */
    public boolean isTraceExplorerVar()
    {
        return isTraceExplorerVar;
    }

    /**
     * Returns the name this variable in a single line String.
     * 
     * The name could be multiple lines if this represents a trace explorer
     * expression.
     * 
     * @return
     */
    public String getSingleLineName()
    {
        return name.replaceAll("\n", "").replaceAll("\r", "");    }

    /**
     * Sets the status of this variable as representing or not
     * representing a trace explorer expression. By default, it
     * is not.
     * 
     * @param isTraceExplorerVar whether or not this variable
     * represents a trace explorer expression.
     */
    public void setTraceExplorerVar(boolean isTraceExplorerVar)
    {
        this.isTraceExplorerVar = isTraceExplorerVar;
    }
	
	public int getChildCount() {
		return value.getChildCount();
	}
	
	public final boolean isChanged() {
		return value.isAdded() || value.isDeleted() || value.isChanged();
	}
}
