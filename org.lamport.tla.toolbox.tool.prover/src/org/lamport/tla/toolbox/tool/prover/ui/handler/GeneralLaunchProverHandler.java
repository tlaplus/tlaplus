package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.tool.prover.ui.dialog.LaunchProverDialog;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Executing this handler opens a dialog that shows a general list of options
 * for launching the prover. The dialog is {@link LaunchProverDialog}. See that
 * class for a more detailed explanation of the dialog.
 * 
 * @author Daniel Ricketts
 *
 */
public class GeneralLaunchProverHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
    	/*
    	 * Check for dirty module added by LL on 14 Dec 2010
    	 */
        boolean proceed = UIHelper.promptUserForDirtyModules();
        if (!proceed)
        {
            // the user cancelled
            return null;
        }
        LaunchProverDialog dialog = new LaunchProverDialog(UIHelper.getShellProvider());
        dialog.open();
        return null;
    }

}
