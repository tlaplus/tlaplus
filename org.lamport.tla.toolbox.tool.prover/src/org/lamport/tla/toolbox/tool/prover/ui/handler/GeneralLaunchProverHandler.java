package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.tool.prover.ui.dialog.LaunchProverDialog;
import org.lamport.tla.toolbox.util.UIHelper;

public class GeneralLaunchProverHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        LaunchProverDialog dialog = new LaunchProverDialog(UIHelper.getShellProvider());
        dialog.open();
        return null;
    }

}
