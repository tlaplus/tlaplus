/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.ui.navigator;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.viewers.AbstractTreeViewer;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.navigator.CommonViewer;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.handler.OpenModuleHandler;
import org.lamport.tla.toolbox.ui.provider.IGroup;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Specification Explorer
 */
public class ToolboxExplorer extends CommonNavigator
{
    public final static String VIEW_ID = "toolbox.view.ToolboxExplorer";
    public static final String COMMAND_ID = "toolbox.command.cnf.open.delegate";
    
	/**
     * Override the method to deliver the root object for the NCE activation
     */
    protected Object getInitialInput()
    {
        return Activator.getSpecManager();
    }

    /**
     * Open on double-click
     */
    protected void handleDoubleClick(DoubleClickEvent anEvent)
    {
        super.handleDoubleClick(anEvent);
        // open the model
        if (anEvent.getSelection() instanceof IStructuredSelection) {
        	IStructuredSelection iss = (IStructuredSelection) anEvent.getSelection();
        	Object firstElement = iss.getFirstElement();
        	if (firstElement instanceof Module) {
        		final Map<String, String> parameters = new HashMap<String, String>();
        		parameters.put(OpenModuleHandler.PARAM_MODULE, ((Module) firstElement).getModuleName());
				UIHelper.runCommand(OpenModuleHandler.COMMAND_ID, parameters);
        	} else if (firstElement instanceof IGroup) {
        		// No-Op
        	} else if (firstElement instanceof Spec && ((Spec) firstElement).isCurrentSpec()) {
        		// No-op, do not re-open an open spec again.
        	} else {
        		UIHelper.runCommand(ToolboxExplorer.COMMAND_ID, new HashMap<String, String>());
        	}
        }
    }

    /**
     * Finds the CommonNavigatorViewer by name
     * @param navigatorViewId
     * @return
     */
    private static CommonNavigator findCommonNavigator(String navigatorViewId)
    {
        IWorkbenchPage page = UIHelper.getActivePage();
        if (page != null)
        {
            IViewPart findView = UIHelper.getActivePage().findView(navigatorViewId);
            if (findView != null && findView instanceof CommonNavigator)
            {
                return ((CommonNavigator) findView);
            }
        }
        return null;
    }

    /**
     * Retrieves the current viewer if any
     * @return the instance of common viewer or <code>null</code>
     */
    public static CommonViewer getViewer()
    {
        CommonNavigator navigator = findCommonNavigator(ToolboxExplorer.VIEW_ID);
        if (navigator != null) 
        {
            final CommonViewer commonViewer = navigator.getCommonViewer();
            commonViewer.setAutoExpandLevel(AbstractTreeViewer.ALL_LEVELS);
			return commonViewer;
        }
        
        return null;
    } 

    /**
     * Refreshes the instance of the viewer if any
     */
    static void refresh()
    {
        CommonViewer instance = getViewer();
        if (instance != null)
        {
            instance.refresh();
        }
    }
//
//    /**
//     * Sets the status of a NCE of the current viwer if any
//     */
//    private static void setToolboxNCEActive(final String extensionId, final boolean active)
//    {
//        CommonNavigator instance = findCommonNavigator(ToolboxExplorer.VIEW_ID);
//        if (instance != null) 
//        {
//            INavigatorContentService contentService = instance.getNavigatorContentService();
//            boolean isActive = contentService.getActivationService().isNavigatorExtensionActive(extensionId);
//            if (active && !isActive)
//            {
//                contentService.getActivationService().activateExtensions(new String[] { extensionId }, false);
//            } else if (!active && isActive)
//            {
//                contentService.getActivationService().deactivateExtensions(new String[] { extensionId }, false);
//            } else
//            {
//                // do nothing, just quit
//                return;
//            }
//            contentService.getActivationService().persistExtensionActivations();
//            contentService.update();
//        }
//    }
}
