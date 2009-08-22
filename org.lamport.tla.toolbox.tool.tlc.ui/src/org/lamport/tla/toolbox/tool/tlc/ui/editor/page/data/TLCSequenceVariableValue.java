package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

import java.util.List;

public class TLCSequenceVariableValue extends TLCSetOrSeqVariableValue {

    private static final String[] DELIMETERS = {"<<", ",", ">>"};

    TLCSequenceVariableValue(List values)
    {
        super(values);
    }

    public String toString()
    {
        TLCVariableValue[] elements = getElements();
        return arrayTosStringBuffer(elements, DELIMETERS).toString();
    }

}
