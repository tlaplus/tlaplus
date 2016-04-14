package org.lamport.tla.toolbox;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.jface.preference.IPreferenceNode;
import org.eclipse.jface.preference.PreferenceManager;
import org.eclipse.swt.dnd.DropTargetListener;
import org.eclipse.swt.graphics.Point;
import org.eclipse.ui.IPluginContribution;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.application.ActionBarAdvisor;
import org.eclipse.ui.application.IActionBarConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;
import org.eclipse.ui.internal.ide.EditorAreaDropAdapter;

/**
 * Configuration of the main window
 */
public class ApplicationWorkbenchWindowAdvisor extends WorkbenchWindowAdvisor
{

    public ApplicationWorkbenchWindowAdvisor(IWorkbenchWindowConfigurer configurer)
    {
        super(configurer);
    }

    public ActionBarAdvisor createActionBarAdvisor(IActionBarConfigurer configurer)
    {
        return new ApplicationActionBarAdvisor(configurer);
    }

    public void preWindowOpen()
    {
        IWorkbenchWindowConfigurer configurer = getWindowConfigurer();
        configurer.setInitialSize(new Point(800, 600));
        configurer.setShowFastViewBars(true);
        configurer.setShowStatusLine(true);
        configurer.setShowProgressIndicator(true);
        configurer.setShowCoolBar(false);
        
        // A DropTargetAdapter is need for editor DND support
        final DropTargetListener dtl = new EditorAreaDropAdapter(
                configurer.getWindow());
        configurer.configureEditorAreaDropListener(dtl);
    }

	/* (non-Javadoc)
	 * @see org.eclipse.ui.application.WorkbenchWindowAdvisor#postWindowOpen()
	 */
	public void postWindowOpen() {
		final PreferenceManager preferenceManager = PlatformUI.getWorkbench().getPreferenceManager();
		final IPreferenceNode[] rootSubNodes = preferenceManager.getRootSubNodes();

		// @see http://bugzilla.tlaplus.net/show_bug.cgi?id=191
		final List filters = new ArrayList();
		filters.add("org.eclipse.compare");
		// The following three preferences are shown because the Toolbox uses
		// the local history feature provided by o.e.team.ui
		filters.add("org.eclipse.team.ui");
		filters.add("org.eclipse.ui.trace");
		filters.add("org.eclipse.jsch.ui");

		// Filter out Pdf4Eclipse preference page.
		filters.add("de.vonloesch.pdf4Eclipse");
		
		// Filter out GraphViz
		//TODO Move its configuration (path to dot) into Toolbox specific preference page.
		filters.add("com.abstratt.graphviz.ui");
		
		// Clean the preferences
		final List elements = preferenceManager.getElements(PreferenceManager.POST_ORDER);
		for (Iterator iterator = elements.iterator(); iterator.hasNext();) {
			final Object elem = (Object) iterator.next();
			if (elem instanceof IPluginContribution) {
				final IPluginContribution aPluginContribution = (IPluginContribution) elem;
				if (filters.contains(aPluginContribution.getPluginId())) {
					final IPreferenceNode node = (IPreferenceNode) elem;

					// remove from root node
					preferenceManager.remove(node);

					// remove from all subnodes
					for (int i = 0; i < rootSubNodes.length; i++) {
						final IPreferenceNode subNode = rootSubNodes[i];
						subNode.remove(node);
					}
				}
			}
		}
		super.postWindowOpen();
		
		// At this point in time we can be certain that the UI is fully
		// instantiated (views, editors, menus...). Thus, register
		// listeners that connect the UI to the workspace resources.
		ToolboxLifecycleParticipantManger.postWorkbenchWindowOpen();
	}
}
