package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

public class TLCUIHelper
{

    /**
     * Registers a control to the context
     * This can only be used within the plug-in org.lamport.tla.toolbox.tool.tlc.ui
     * @param control control to register 
     * @param localContext the context id relative to plug-in ID org.lamport.tla.toolbox.tool.tlc.ui
     * <br>
     * Note: there should be a corresponding context ID defined in the contexts.xml defining the context for current ID. 
     */
    public static void setHelp(Control control, String localContext)
    {
        PlatformUI.getWorkbench().getHelpSystem().setHelp(control, TLCUIActivator.PLUGIN_ID + "." + localContext);
    }

}
