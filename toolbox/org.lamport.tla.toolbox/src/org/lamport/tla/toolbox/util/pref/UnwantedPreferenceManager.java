package org.lamport.tla.toolbox.util.pref;

import org.eclipse.jface.preference.IPreferenceNode;
import org.eclipse.jface.preference.PreferenceManager;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.lifecycle.ToolboxLifecycleParticipant;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.ui.intro.ToolboxIntroPart;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * This class removes unwanted preference pages that are declared
 * by eclipse plug-ins, i.e. plug-ins outside of our control.
 * It is a ToolboxLifeCycleParticipant. The removing of the preference
 * pages occurs in the method initialize which is called by 
 * the ToolboxLifecycleParticipantManager at some point after
 * the toolbox starts up.
 * 
 * @author Dan Ricketts
 *
 */
public class UnwantedPreferenceManager extends ToolboxLifecycleParticipant
{

    public UnwantedPreferenceManager()
    {
        // TODO Auto-generated constructor stub
    }

    public void initialize()
    {
        if (Activator.getDefault().getWorkbench() == null)
        {
            return;
        }
        PreferenceManager pm = Activator.getDefault().getWorkbench().getPreferenceManager();

        if (pm != null)
        {
            /*
             * Subpages need to be removed by calling the remove method
             * on their parent. Pages with no parent can be removed
             * by calling the remove method on the preference manager.
             * 
             * Getting the appropriate id of the page to remove can be done
             * using the code that is commented at the end of this method.
             * It will print out the name followed by the id of every preference page.
             */
            IPreferenceNode generalNode = pm.find("org.eclipse.ui.preferencePages.Workbench");
            if (generalNode != null)
            {
                // these are sub pages of general that we want removed
                generalNode.remove("org.eclipse.ui.preferencePages.Workspace");
                generalNode.remove("org.eclipse.ui.preferencePages.ContentTypes");
                // We no longer want to remove this node.
                // We only want to remove one of its sub nodes.
                // generalNode.remove("org.eclipse.ui.preferencePages.Views");
                // we only want to remove some subnodes of the Editors page
                IPreferenceNode editorsNode = generalNode.findSubNode("org.eclipse.ui.preferencePages.Editors");
                if (editorsNode != null)
                {
                    // remove File Associations page
                    editorsNode.remove("org.eclipse.ui.preferencePages.FileEditors");
                    // want to remove only some subnodes of the Text Editors page
                    IPreferenceNode textEditorsNode = editorsNode
                            .findSubNode("org.eclipse.ui.preferencePages.GeneralTextEditor");
                    if (textEditorsNode != null)
                    {
                        textEditorsNode.remove("org.eclipse.ui.editors.preferencePages.Spelling");
                        textEditorsNode.remove("org.eclipse.ui.editors.preferencePages.QuickDiff");
                        textEditorsNode.remove("org.eclipse.ui.editors.preferencePages.LinkedModePreferencePage");
                    }
                }
                generalNode.remove("org.eclipse.ui.preferencePages.Perspectives");
                generalNode.remove("org.eclipse.equinox.security.ui.category");
                IPreferenceNode appearanceNode = generalNode.findSubNode("org.eclipse.ui.preferencePages.Views");
                if (appearanceNode != null)
                {
                    // Removes the label decorators node that is a sub node of
                    // the appearance node.
                    // We want to keep the other sub node, colors and fonts
                    // because it allows for setting the font for
                    // the module editor.
                    appearanceNode.remove("org.eclipse.ui.preferencePages.Decorators");
                }
            }

            // remove Install/Update
            pm.remove("org.eclipse.equinox.internal.p2.ui.sdk.ProvisioningPreferencePage");

            // remove the sub node of help
            IPreferenceNode helpNode = pm.find("org.eclipse.help.ui.browsersPreferencePage");
            if (helpNode != null)
            {
                helpNode.remove("org.eclipse.help.ui.contentPreferencePage");
            }
        }
    }

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.lifecycle.ToolboxLifecycleParticipant#terminate()
	 */
	public void terminate() {
		if (!ToolboxHandle.getInstanceStore().getBoolean(ToolboxHandle.I_RESTORE_LAST_SPEC)) {
			UIHelper.getActivePage().closeAllEditors(true);
			UIHelper.switchPerspective(ToolboxIntroPart.PERSPECTIVE_ID);
		}
	}
}
