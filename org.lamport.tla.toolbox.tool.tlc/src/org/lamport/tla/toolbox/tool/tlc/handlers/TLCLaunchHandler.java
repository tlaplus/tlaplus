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

import tlc2.TLC;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class TLCLaunchHandler extends AbstractHandler {
	/**
	 * The constructor.
	 */
	public TLCLaunchHandler() {
	}

	/**
	 * the command has been executed, so extract extract the needed information
	 * from the application context.
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindowChecked(event);
		MessageDialog.openInformation(
				window.getShell(),
				"TLA+ Toolbox TLC",
				"TLC Launch executed");
		
		
		IFile rootModule = ToolboxHandle.getRootModule();
		
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
		    TLC.main(new String[]{"-config", cfgFile.getPath(), rootModule.toString()});
		}
		return null;
	}
}
