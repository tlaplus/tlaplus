package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.swt.SWT;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.actions.CompoundContributionItem;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.lamport.tla.toolbox.tool.tlc.handlers.OpenSavedModuleHandler;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * This class is used to populate a menu with items that represent the versions
 * of modules saved in a run of TLC. Selecting an item opens the module in a
 * read-only editor as a page in the model editor.
 * 
 * @author Daniel Ricketts
 * 
 */
public class SavedModuleContributionItem extends CompoundContributionItem
{

    public SavedModuleContributionItem()
    {
        // TODO Auto-generated constructor stub
    }

    public SavedModuleContributionItem(String id)
    {
        super(id);
        // TODO Auto-generated constructor stub
    }

    protected IContributionItem[] getContributionItems()
    {
        /*
         * Does nothing if the active editor is not a model editor. The
         * following code gets the config file for the active model editor (if
         * it is the active editor), gets the model folder for that config,
         * iterates through all members of the model folder, adding a
         * contribution item for each member that has extension .tla and is not
         * TE.tla or MC.tla.
         */
        IEditorPart editor = UIHelper.getActiveEditor();
        if (editor instanceof ModelEditor)
        {
            ModelEditor modelEditor = (ModelEditor) editor;
            IFolder modelFolder = ModelHelper.getModelTargetDirectory(modelEditor.getConfig());
            if (modelFolder != null && modelFolder.exists())
            {
                try
                {
                    /*
                     * The collection of command contribution items that will
                     * populate the menu and contain the command to be run when
                     * selected.
                     */
                    final List<IContributionItem> contributions = new ArrayList<IContributionItem>();

                    // get all resources in the model folder
                    IResource[] members = modelFolder.members();
                    for (int i = 0; i < members.length; i++)
                    {
                        /*
                         * We add to the menu an option to open every file that
                         * has exists, has extension .tla, and is not the TE or
                         * MC file.
                         * 
                         * On Nov 2011, DR added a null check to members[i].getFileExtension() which
                         * can return null for directories.
                         */
                        if (members[i].exists() && members[i].getFileExtension() != null
                                && members[i].getFileExtension().equals(ResourceHelper.TLA_EXTENSION)
                                && !members[i].getName().equals(ModelHelper.FILE_TLA)
                                && !members[i].getName().equals(ModelHelper.TE_FILE_TLA))
                        {
                            Map<String, String> parameters = new HashMap<String, String>(1);
                            parameters.put(OpenSavedModuleHandler.PARAM_MODULE_PATH, members[i].getRawLocation()
                                    .toPortableString());
                            contributions.add(new CommandContributionItem(new CommandContributionItemParameter(UIHelper
                                    .getActiveWindow(), "toolbox.command.model.open.savedModule.",
                                    OpenSavedModuleHandler.COMMAND_ID, parameters, null, null, null, members[i]
                                            .getName(), null, "Opens the version saved in the last run of TLC.",
                                    SWT.PUSH, null, true)));
                        }
                    }

                    return (IContributionItem[]) contributions.toArray(new IContributionItem[contributions.size()]);
                } catch (CoreException e)
                {
                    TLCUIActivator.getDefault().logError("Error getting members of model folder " + modelFolder, e);
                }
            }
        }
        return new IContributionItem[0];
    }
}
