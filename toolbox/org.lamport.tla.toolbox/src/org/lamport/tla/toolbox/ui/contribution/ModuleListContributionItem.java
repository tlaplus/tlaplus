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
package org.lamport.tla.toolbox.ui.contribution;

import java.util.HashMap;
import java.util.Vector;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.actions.CompoundContributionItem;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.handler.AddModuleHandler;
import org.lamport.tla.toolbox.ui.handler.OpenModuleHandler;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tlc2.output.SpecWriterUtilities;

/**
 * Contribution item for opening the modules
 */
public class ModuleListContributionItem extends CompoundContributionItem
{
    private ImageDescriptor rootIcon = UIHelper.imageDescriptor("icons/full/obj16/ftr_mf_obj.gif");
    private ImageDescriptor icon = UIHelper.imageDescriptor("icons/full/obj16/file_obj.gif");
    private ImageDescriptor iconAddModule = UIHelper.imageDescriptor("icons/full/newmodule_wiz.gif");    

    
    /**
     * @see org.eclipse.ui.actions.CompoundContributionItem#getContributionItems()
     */
    protected IContributionItem[] getContributionItems()
    {
        final Spec spec = Activator.getSpecManager().getSpecLoaded();
        final Vector<IContributionItem> moduleContributions = new Vector<IContributionItem>();
        HashMap<String, String> parameters = new HashMap<String, String>();
        
        // create the contribution item for add module
        CommandContributionItemParameter param = new CommandContributionItemParameter(UIHelper.getActiveWindow(),
                "toolbox.command.module.add", AddModuleHandler.COMMAND_ID, parameters, iconAddModule, null, null,
                "Add TLA+ Module...", null, "Adds new TLA+ Module to the specification",
                CommandContributionItem.STYLE_PUSH, null, true);

        // add contribution item to the list
        moduleContributions.add(new CommandContributionItem(param));
        moduleContributions.add(new Separator());

        if (spec != null)
        {
            final IResource[] modules = spec.getModuleResources();
            final IResource rootModule = spec.getRootFile();
            boolean isRoot;
            for (int i = 0; i < modules.length; i++)
            {
                // skip non-modules and non-existing files
                if (!ResourceHelper.isModule(modules[i]))
                {
                    continue;
                } 
                

                isRoot = rootModule.equals(modules[i]);

                parameters = new HashMap<String, String>();
                // fill the module name for the handler
                parameters.put(OpenModuleHandler.PARAM_MODULE, SpecWriterUtilities.getModuleNameChecked(
                        modules[i].getName(), false));

                // create the contribution item
                param = new CommandContributionItemParameter(UIHelper.getActiveWindow(), "toolbox.command.module.open."
                        + modules[i].getName(), OpenModuleHandler.COMMAND_ID, parameters, ((isRoot) ? rootIcon : icon),
                        null, null, modules[i].getName(), null, "Opens " + modules[i].getName(),
                        CommandContributionItem.STYLE_PUSH, null, true);

                // add contribution item to the list
                moduleContributions.add(new CommandContributionItem(param));
            }
        }
        return (IContributionItem[]) moduleContributions.toArray(new IContributionItem[moduleContributions.size()]);
    }
}
