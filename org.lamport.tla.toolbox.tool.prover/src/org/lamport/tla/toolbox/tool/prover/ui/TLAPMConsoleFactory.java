package org.lamport.tla.toolbox.tool.prover.ui;

import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleFactory;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Used in the extension point org.eclipse.ui.console.ConsoleFactories
 * for creating a console for the TLAPM.
 * 
 * The method {@link TLAPMConsoleFactory#openConsole()} is specified
 * by the interface and is used to create/open the console.
 * 
 * The method {@link TLAPMConsoleFactory#getTLAPMConsole()} can be used
 * by other class to get the console for the TLAPM.
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAPMConsoleFactory implements IConsoleFactory
{

    /**
     * The name used to register the console so that it can
     * later be found using {@link TLAPMConsoleFactory#getTLAPMConsole()}
     */
    private static final String TLAPM_CONSOLE_ID = "TLAPM-Console";

    /**
     * Opens a generic console view using {@link TLAPMConsoleFactory#TLAPM_CONSOLE_ID} as the
     * console name so that it can be found later.
     */
    public void openConsole()
    {
        IWorkbenchPage activePage = UIHelper.getActivePage();
        if (activePage != null)
        {
            try
            {
                activePage.showView(IConsoleConstants.ID_CONSOLE_VIEW, TLAPM_CONSOLE_ID, IWorkbenchPage.VIEW_ACTIVATE);
            } catch (PartInitException e)
            {
                ConsolePlugin.log(e);
            }
        }
    }

    /**
     * Returns a handle on the console for
     * the TLAPM.
     * @return
     */
    public static MessageConsole getTLAPMConsole()
    {
        MessageConsole console = findConsole(TLAPM_CONSOLE_ID);

        return console;
    }

    /**
     * Finds the console with a given name.
     * 
     * @param name, name of the console
     * @return
     */
    private static MessageConsole findConsole(String name)
    {
        if (name == null)
        {
            throw new IllegalArgumentException("Console name must be not null");
        }
        IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();

        IConsole[] existing = consoleManager.getConsoles();
        // try to find existing
        for (int i = 0; i < existing.length; i++)
        {
            if (name.equals(existing[i].getName()))
            {
                return (MessageConsole) existing[i];
            }
        }

        // no console found, create a new one
        MessageConsole myConsole = new MessageConsole(name, null);
        consoleManager.addConsoles(new IConsole[] { myConsole });
        return myConsole;
    }

}
