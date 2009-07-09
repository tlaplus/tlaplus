package org.lamport.tla.toolbox;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;

/**
 * This class controls all aspects of the application's execution
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Application implements IApplication
{

    /* (non-Javadoc)
     * @see org.eclipse.equinox.app.IApplication#start(org.eclipse.equinox.app.IApplicationContext)
     */
    public Object start(IApplicationContext context)
    {
        Object argObject = context.getArguments().get(IApplicationContext.APPLICATION_ARGS);
        if (argObject != null && argObject instanceof String[])
        {
            String[] args = (String[]) argObject;
            if (args.length != 0)
            {
                System.out.println(context.getBrandingName() + " started with " + args.length + " arguments.");
                for (int i = 0; i < args.length; i++)
                {
                    System.out.println(args[i] + ((i == args.length - 1) ? "" : ", "));
                }
            } else
            {
                System.out.println(context.getBrandingName() + " started without arguments.");
            }
        }

        Display display = PlatformUI.createDisplay();
        try
        {
            int returnCode = PlatformUI.createAndRunWorkbench(display, new ApplicationWorkbenchAdvisor());
            if (returnCode == PlatformUI.RETURN_RESTART)
            {
                return IApplication.EXIT_RESTART;
            }
            return IApplication.EXIT_OK;
        } finally
        {
            display.dispose();
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.equinox.app.IApplication#stop()
     */
    public void stop()
    {
        final IWorkbench workbench = PlatformUI.getWorkbench();
        if (workbench == null)
            return;
        final Display display = workbench.getDisplay();
        display.syncExec(new Runnable() {
            public void run()
            {
                if (!display.isDisposed())
                    workbench.close();
            }
        });
    }
}
