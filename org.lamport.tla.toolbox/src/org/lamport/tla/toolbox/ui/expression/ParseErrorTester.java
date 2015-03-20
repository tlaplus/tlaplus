package org.lamport.tla.toolbox.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.util.AdapterFactory;

/**
 * This is used to test whether or not the Parse Errors menu item
 * should be active.
 */
public class ParseErrorTester extends PropertyTester {

	/* (non-Javadoc)
	 * @see org.eclipse.core.expressions.IPropertyTester#test(java.lang.Object, java.lang.String, java.lang.Object[], java.lang.Object)
	 */
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		if (Activator.isSpecManagerInstantiated()) {
			WorkspaceSpecManager specManager = Activator.getSpecManager();
			if (specManager != null) {
				Spec loadedSpec = specManager.getSpecLoaded();
				if (loadedSpec != null) {
					return AdapterFactory.isProblemStatus(loadedSpec.getStatus());
				}
			}
		}
		return false;
	}
}
