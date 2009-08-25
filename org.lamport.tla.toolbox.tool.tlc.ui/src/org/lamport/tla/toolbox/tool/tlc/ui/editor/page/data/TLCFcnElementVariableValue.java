package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

/**
 * Represents a pair of TLCVariableValue objects; used to hold individual
 *  mappings of a function--the individual ordered pairs if a function were
 *  a set of ordered pairs.  The object O represents O.from @@ O.value
 * @author lamport
 *
 */
public class TLCFcnElementVariableValue extends TLCVariableValue {
    protected TLCVariableValue from ;
    public TLCVariableValue getFrom(){
        return from;
    }

    /**
     * 
     */
    public TLCFcnElementVariableValue(TLCVariableValue fromVal, TLCVariableValue toVal) {
        from = fromVal ;
        value = toVal ;
        // TODO Auto-generated constructor stub
    }

    public String toString() {
        return from.toString() + " :> " + value.toString();
    }
}
