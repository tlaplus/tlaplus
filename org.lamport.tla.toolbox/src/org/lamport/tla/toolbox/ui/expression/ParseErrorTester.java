package org.lamport.tla.toolbox.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.util.AdapterFactory;

/**
 * This was previously used to test whether or not the Parse Errors
 * menu item should be active. This is now done in WorkspaceSpecManager
 * in the method {@link WorkspaceSpecManager#specParsed(Spec)}.
 * 
 * @author drickett
 *
 */
public class ParseErrorTester extends PropertyTester
{

    public ParseErrorTester()
    {
        // TODO Auto-generated constructor stub
    }

    public boolean test(Object receiver, String property, Object[] args, Object expectedValue)
    {
        if (Activator.isSpecManagerInstantiated())
        {
            WorkspaceSpecManager specManager = Activator.getSpecManager();
            if (specManager != null)
            {
                Spec loadedSpec = specManager.getSpecLoaded();
                if (loadedSpec != null)
                {
                    return AdapterFactory.isProblemStatus(loadedSpec.getStatus());
                }
            }
        }
        return false;
    }

}
