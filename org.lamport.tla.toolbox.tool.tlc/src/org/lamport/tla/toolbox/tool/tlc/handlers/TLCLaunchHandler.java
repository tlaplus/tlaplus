package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.RCPNameToFileIStream;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tlc2.TLC;
import util.ToolIO;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class TLCLaunchHandler extends AbstractHandler
{
    /**
     * The constructor.
     */
    public TLCLaunchHandler()
    {
    }

    /**
     * the command has been executed, so extract extract the needed information
     * from the application context.
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindowChecked(event);
        MessageDialog.openInformation(window.getShell(), "TLA+ Toolbox TLC", "TLC Launch executed");

        IFile rootModule = ToolboxHandle.getRootModule();

        String rootFilename = rootModule.getLocation().toOSString();
        // TODO HACK
        String cfgPath = rootModule.getLocation().removeFileExtension().addFileExtension("cfg").toOSString();
        File cfgFile = new File(cfgPath);
        if (!cfgFile.exists())
        {
            try
            {
                cfgFile.createNewFile();
            } catch (IOException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        if (rootModule != null)
        {
            // Reset the tool output messages.
            ToolIO.reset();
            ToolIO.setMode(ToolIO.TOOL);

            ToolIO.setUserDir(ResourceHelper.getParentDir(rootModule.getLocation().toOSString()));

            // create a TLC instance
            TLC tlc = new TLC();

            // setup name resolver
            tlc.setResolver(new RCPNameToFileIStream(null));

            // handle parameters
            // tlc.handleParameters(new String[]{"-config", cfgFile.getPath(),
            // ResourceHelper.getModuleName(rootFilename)});
            tlc.handleParameters(new String[] { ResourceHelper.getModuleName(rootFilename) });

            // call the actual processing method
            tlc.process();

            String[] messages = ToolIO.getAllMessages();
            for (int i = 0; i < messages.length; i++)
            {
                System.out.println(messages[i]);
            }
        }
        return null;
    }
}
