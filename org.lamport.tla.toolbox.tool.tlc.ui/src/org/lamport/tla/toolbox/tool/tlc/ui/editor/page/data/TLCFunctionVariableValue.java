package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

import java.util.List;

/*************************************************************
 * Represents a function as a list of TLCFcnElementVariable objects
 * 
 * @author lamport
 *
 */
public class TLCFunctionVariableValue extends TLCVariableValue {

    private static final String[] DELIMETERS = { "(", " @@", ")" };

    /**
     * @param fcnElements
     */
    public TLCFunctionVariableValue(List fcnElements)
    {
        this.value = fcnElements;
    }
  
    public Object getValue()
    {
        return getFcnElements();
    }
 
    public TLCFcnElementVariableValue[] getFcnElements()
    {
        return (TLCFcnElementVariableValue[]) 
                  ((List) this.value).toArray(new TLCFcnElementVariableValue[((List) this.value)
                    .size()]);
    }
    public String toString()
    {
        return arrayToStringBuffer(getFcnElements(), DELIMETERS).toString();
    }
}
