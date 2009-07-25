package org.lamport.tla.toolbox.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class CurrentSpecTester extends PropertyTester
{

    /**
     * Tests if the spec is currently selected
     */
    public boolean test(Object receiver, String property, Object[] args, Object expectedValue)
    {
        if ("isCurrentSpec".equals(property))
        {
            if (receiver != null && receiver instanceof Spec) 
            {
                Spec spec = (Spec) receiver;
                Spec current = ToolboxHandle.getCurrentSpec();
                if (current == spec) 
                {
                    return true;
                }
            }
        }        
        return false;
    }

}
