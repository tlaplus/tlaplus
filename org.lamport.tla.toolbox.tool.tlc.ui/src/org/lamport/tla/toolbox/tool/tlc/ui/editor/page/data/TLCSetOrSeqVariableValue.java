package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

import java.util.List;

public class TLCSetOrSeqVariableValue extends TLCVariableValue {

    
    TLCSetOrSeqVariableValue(List values)
    {
        this.value = values;
    }
    
    public Object getValue() 
    {
        return getElements();
    }

    public TLCVariableValue[] getElements()
    {
        List list = (List)value; 
        return (TLCVariableValue[])list.toArray(new TLCVariableValue[list.size()]);
    }
    
    
}
