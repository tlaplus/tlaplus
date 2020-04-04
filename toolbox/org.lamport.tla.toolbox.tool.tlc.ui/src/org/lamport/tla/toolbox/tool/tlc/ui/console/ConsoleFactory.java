package org.lamport.tla.toolbox.tool.tlc.ui.console;

import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleFactory;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.IOConsole;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A TLC console
 * @author Simon Zambrovski
 */
public class ConsoleFactory implements IConsoleFactory
{
    private static final String TLC_ID = "TLC-Console";

    public void openConsole()
    {
        IWorkbenchPage activePage = UIHelper.getActivePage();
        if (activePage != null)
        {
            try
            {
                activePage.showView(IConsoleConstants.ID_CONSOLE_VIEW, TLC_ID, IWorkbenchPage.VIEW_ACTIVATE);
            } catch (PartInitException e)
            {
                ConsolePlugin.log(e);
            }
        }
    }

    public static IOConsole getTLCConsole()
    {
    	IOConsole console = findConsole(TLC_ID);

        return console;
    }

    /**
     * Fins the console with a given name
     * @param name, name of the console
     * @return
     */
    private static IOConsole findConsole(String name)
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
                return (IOConsole) existing[i];
            }
        }

        // no console found, create a new one
        IOConsole myConsole = new IOConsole(name, null);
        consoleManager.addConsoles(new IConsole[] { myConsole });
        return myConsole;
    }

}
