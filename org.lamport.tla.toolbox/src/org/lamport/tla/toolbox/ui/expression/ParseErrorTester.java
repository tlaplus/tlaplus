package org.lamport.tla.toolbox.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.util.AdapterFactory;

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
