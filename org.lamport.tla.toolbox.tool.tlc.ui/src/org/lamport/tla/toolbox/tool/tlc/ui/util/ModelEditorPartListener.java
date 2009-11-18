package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * This is used to update the error view
 * when a model editor is made visible.
 * 
 * This is done in the partVisible() method.
 * 
 * This is a singleton, accessed by the method
 * getDefault(). It is a singleton because it is
 * added as a listener each time a model editor is created,
 * in the init() method. We don't want a copy
 * of the same listener added more than once, so it is
 * a singleton.
 * 
 * @author Dan Ricketts
 *
 */
public class ModelEditorPartListener implements IPartListener2
{
    private static ModelEditorPartListener listener;

    public ModelEditorPartListener()
    {
        // TODO Auto-generated constructor stub
    }
    
    public static ModelEditorPartListener getDefault()
    {
        if (listener == null)
        {
            listener = new ModelEditorPartListener();
        }
        return listener;
    }

    public void partActivated(IWorkbenchPartReference partRef)
    {
        // TODO Auto-generated method stub

    }

    public void partBroughtToTop(IWorkbenchPartReference partRef)
    {
        // TODO Auto-generated method stub

    }

    public void partClosed(IWorkbenchPartReference partRef)
    {
        // TODO Auto-generated method stub

    }

    public void partDeactivated(IWorkbenchPartReference partRef)
    {
        // TODO Auto-generated method stub

    }

    public void partHidden(IWorkbenchPartReference partRef)
    {
        // TODO Auto-generated method stub

    }

    public void partInputChanged(IWorkbenchPartReference partRef)
    {
        // TODO Auto-generated method stub

    }

    public void partOpened(IWorkbenchPartReference partRef)
    {
        // TODO Auto-generated method stub

    }

    /**
     * This updates the error view. If the error view is not open,
     * then the user may have closed it, so nothing is done.
     * If the error view is open but the model editor being switched
     * to has no errors, then the error view is cleared but not closed.
     * If the model editor made visible does have errors, then the error
     * view is updated with these errors.
     */
    public void partVisible(IWorkbenchPartReference partRef)
    {
        IWorkbenchPart part = partRef.getPart(false);

        if (part != null && part instanceof ModelEditor)
        {
            ModelEditor editor = (ModelEditor) part;
            TLCModelLaunchDataProvider provider = (TLCModelLaunchDataProvider) editor
                    .getAdapter(TLCModelLaunchDataProvider.class);
            TLCErrorView errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
            if (errorView != null && provider != null)
            {
                if (provider.getErrors().size() > 0)
                {
                    TLCErrorView.updateErrorView(provider);
                } else
                {
                    errorView.clear();
                }
            }
        }
    }

}
