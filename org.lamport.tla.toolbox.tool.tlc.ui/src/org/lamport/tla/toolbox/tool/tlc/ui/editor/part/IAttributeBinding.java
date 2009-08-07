package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

/**
 * Provides the interface for binding of attributes to the fields
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IAttributeBinding
{
    /**
     * Binds a control to the attribute
     * @param attributeName name of the attribute
     * @param control the control taking care of its display and editing
     */
    public void bindAttribute(String attributeName, Object control);
    
    /**
     * Retrieves the control handling the current attribute name of the attribute 
     */
    public Object getAttributeControl(String attributeName);
    
    /**
     * Retrieves the id of the binding 
     * @return String index representing the binding
     */
    public String getBindingId(); 
}
