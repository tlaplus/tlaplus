package org.lamport.tla.toolbox;

import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;
import org.eclipse.ui.application.ActionBarAdvisor;
import org.eclipse.ui.application.IActionBarConfigurer;

/**
 * An action bar advisor is responsible for creating, adding, and disposing of
 * the actions added to a workbench window. Each window will be populated with
 * new actions.
 */
public class ApplicationActionBarAdvisor extends ActionBarAdvisor
{
    private IWorkbenchAction helpContentsAction;
    // private IWorkbenchAction aboutAction;
    // private IWorkbenchAction helpSearchAction;
    // private IWorkbenchAction dynamicHelpAction;

    private IWorkbenchAction quitAction;
    private IWorkbenchAction saveAction;
    private IWorkbenchAction saveAsAction;

    private IWorkbenchAction preferencesAction;

    // private IWorkbenchAction newEditorAction;
    // private IWorkbenchAction newWindowAction;
    private IWorkbenchAction resetPerspectiveAction;
	private IWorkbenchAction backwardHistoryAction;
	private IWorkbenchAction forwardHistoryAction;

    /**
     * @param configurer
     */
    public ApplicationActionBarAdvisor(IActionBarConfigurer configurer)
    {
        super(configurer);
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.application.ActionBarAdvisor#makeActions(org.eclipse.ui.IWorkbenchWindow)
     */
    protected void makeActions(IWorkbenchWindow window)
    {
        helpContentsAction = ActionFactory.HELP_CONTENTS.create(window);
        register(helpContentsAction);

        // helpSearchAction = ActionFactory.HELP_SEARCH.create(window);
        // register(helpSearchAction);

        // dynamicHelpAction = ActionFactory.DYNAMIC_HELP.create(window);
        // register(dynamicHelpAction);

        // aboutAction = ActionFactory.ABOUT.create(window);
        // register(aboutAction);

        quitAction = ActionFactory.QUIT.create(window);
        register(quitAction);

        saveAction = ActionFactory.SAVE.create(window);
        register(saveAction);

        saveAsAction = ActionFactory.SAVE_AS.create(window);
        register(saveAsAction);

        preferencesAction = ActionFactory.PREFERENCES.create(window);
        register(preferencesAction);

        /*
        newEditorAction = ActionFactory.NEW_EDITOR.create(window);
        register(newEditorAction);
        */
        /*
        newWindowAction = ActionFactory.OPEN_NEW_WINDOW.create(window);
        newWindowAction.setText("New Toolbox window");
        register(newWindowAction);
        */

        resetPerspectiveAction = ActionFactory.RESET_PERSPECTIVE.create(window);
        register(resetPerspectiveAction);
        
        backwardHistoryAction = ActionFactory.BACKWARD_HISTORY
                .create(window);
        register(backwardHistoryAction);
        
        forwardHistoryAction= ActionFactory.FORWARD_HISTORY
                .create(window);
        register(forwardHistoryAction);

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.application.ActionBarAdvisor#fillMenuBar(org.eclipse.jface.action.IMenuManager)
     */
    protected void fillMenuBar(final IMenuManager menuBar) {

    	// File menu
        final MenuManager fileMenu = new MenuManager("&File", "toolbox.file.menu");
        fileMenu.add(new Separator("toolbox.file.spec.separator"));
        fileMenu.add(new Separator("toolbox.file.module.separator"));
        fileMenu.add(new Separator("toolbox.file.translation.separator"));
        fileMenu.add(new Separator("toolbox.file.save.separator"));
        fileMenu.add(saveAction);
        fileMenu.add(saveAsAction);
        fileMenu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
        fileMenu.add(preferencesAction);
        fileMenu.add(new Separator());
        fileMenu.add(quitAction);

        // Window Menu
        final MenuManager windowMenu = new MenuManager("&Window", "toolbox.window.menu");
        windowMenu.add(new Separator("toolbox.window.open.separator"));
        windowMenu.add(new Separator());
        windowMenu.add(new Separator("toolbox.window.tools.separator"));
        windowMenu.add(new Separator());
        windowMenu.add(new Separator("toolbox.window.view.separator"));
        windowMenu.add(new Separator());

        windowMenu.add(backwardHistoryAction);
        windowMenu.add(forwardHistoryAction);

        // Menu bar contributions via plugin.xmls
        final Separator separator = new Separator("toolbox.tools.separator");
        separator.setVisible(false); // @see http://bugzilla.tlaplus.net/show_bug.cgi?id=27

        // finally add to menu bar
        menuBar.add(fileMenu);
        menuBar.add(windowMenu);
		menuBar.add(separator);
    }
}
