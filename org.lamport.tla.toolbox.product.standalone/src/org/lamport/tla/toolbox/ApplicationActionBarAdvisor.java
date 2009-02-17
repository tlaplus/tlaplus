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
    private IWorkbenchAction aboutAction;
    private IWorkbenchAction helpSearchAction;
    private IWorkbenchAction dynamicHelpAction;

    private IWorkbenchAction quitAction;
    private IWorkbenchAction saveAction;

    // private IWorkbenchAction saveAsAction;

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

        helpSearchAction = ActionFactory.HELP_SEARCH.create(window);
        register(helpSearchAction);

        dynamicHelpAction = ActionFactory.DYNAMIC_HELP.create(window);
        register(dynamicHelpAction);

        aboutAction = ActionFactory.ABOUT.create(window);
        register(aboutAction);

        quitAction = ActionFactory.QUIT.create(window);
        register(quitAction);

        saveAction = ActionFactory.SAVE.create(window);
        saveAction.setText("Save Module");
        register(saveAction);

        // saveAsAction = ActionFactory.SAVE_AS.create(window);
        // register(saveAsAction);

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.application.ActionBarAdvisor#fillMenuBar(org.eclipse.jface.action.IMenuManager)
     */
    protected void fillMenuBar(IMenuManager menuBar)
    {
        MenuManager fileMenu = new MenuManager("&File", "toolbox.file.menu");
        // place holder for spec actions
        fileMenu.add(new Separator("toolbox.file.spec.separator"));
        // place holder for module actions
        fileMenu.add(new Separator("toolbox.file.module.separator"));
        
        fileMenu.add(saveAction);

        // fileMenu.add(saveAsAction);

        // place holder for other actions
        fileMenu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
        fileMenu.add(new Separator());
        fileMenu.add(quitAction);

        MenuManager toolsMenu = new MenuManager("&Tools", "toolbox.tools.menu");
        toolsMenu.add(new Separator("toolbox.tools.separator"));
        toolsMenu.add(new Separator("toolbox.toolmenus.separator"));

        /*
        MenuManager helpMenu = new MenuManager("&Help", IWorkbenchActionConstants.M_HELP);

        // Help Contents
        helpMenu.add(helpContentsAction);
        // Help Search
        helpMenu.add(helpSearchAction);
        // Additions
        helpMenu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
        // About action
        helpMenu.add(aboutAction);
        */

        menuBar.add(fileMenu);
        menuBar.add(toolsMenu);
        menuBar.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
        // menuBar.add(dynamicHelpAction);
        // menuBar.add(helpMenu);
    }

}
