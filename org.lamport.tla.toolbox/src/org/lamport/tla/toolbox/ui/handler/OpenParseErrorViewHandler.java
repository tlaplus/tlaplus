package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.ui.view.ProblemView;
import org.lamport.tla.toolbox.util.UIHelper;

public class OpenParseErrorViewHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        HashMap params = new HashMap();
        params.put(OpenViewHandler.PARAM_VIEW_NAME, ProblemView.ID);
        UIHelper.runCommand(OpenViewHandler.COMMAND_ID, params);

        return null;
    }

}
