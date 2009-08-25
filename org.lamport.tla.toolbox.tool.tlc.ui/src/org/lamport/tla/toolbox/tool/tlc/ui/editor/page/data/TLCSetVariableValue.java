package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

import java.util.List;

public class TLCSetVariableValue extends TLCSetOrSeqVariableValue {

    
    private static final String[] DELIMETERS = {"{", ",", "}"};

    TLCSetVariableValue(List values)
    {
        super(values);
    }
    
    public String toString()
    {
        TLCVariableValue[] elements = getElements();
        return arrayToStringBuffer(elements, DELIMETERS).toString();
    }
}
