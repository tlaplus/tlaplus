package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
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

	public static ModelEditorPartListener getDefault() {
		if (listener == null) {
			listener = new ModelEditorPartListener();
		}
		return listener;
	}

	public void partActivated(IWorkbenchPartReference partRef) {
		// ignored
	}

	public void partBroughtToTop(IWorkbenchPartReference partRef) {
		// ignored
	}

	public void partClosed(IWorkbenchPartReference partRef) {
		// ignored
	}

	public void partDeactivated(IWorkbenchPartReference partRef) {
		// ignored
	}

	public void partHidden(IWorkbenchPartReference partRef) {
		// ignored
	}

	public void partInputChanged(IWorkbenchPartReference partRef) {
		// ignored
	}

	public void partOpened(IWorkbenchPartReference partRef) {
		// ignored
	}

    /**
     * This updates the error view. If the error view is not open,
     * then the user may have closed it, so nothing is done.
     * If the error view is open but the model editor being switched
     * to has no errors, then the error view is cleared but not closed.
     * If the model editor made visible does have errors, then the error
     * view is updated with these errors.
     */
	public void partVisible(final IWorkbenchPartReference partRef)
    {
        final IWorkbenchPart part = partRef.getPart(false);
        
		if (part != null && part instanceof ModelEditor) {
			final ModelEditor editor = (ModelEditor) part;
			TLCModelLaunchDataProvider provider = null;

			final ILaunchConfiguration config = editor.getConfig().getOriginal();

			try {
				if (ModelHelper.isOriginalTraceShown(config)) {
					provider = TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(config);
				} else {
					provider = TLCOutputSourceRegistry.getTraceExploreSourceRegistry().getProvider(config);
				}
			} catch (final CoreException e) {
				TLCUIActivator.getDefault().logError(
						"Error determining if original trace should be shown when model editor is made visible.", e);
			}

			final TLCErrorView errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
			if (errorView != null && provider != null) {
				if (provider.getErrors().size() > 0) {
					// Tell the TLCErrorView update function to not open the
					// TLCErrorView iff the ModelEditor and the TLCErrorView
					// would open in the same part stack (on top of each other).
					// This prevents a stackoverflow that results from cyclic
					// focus activation when the ModelEditor triggers the
					// TLCErrorView to be opened while ModelEditor itself
					// becomes visible (see partVisible()).
					//
					// The steps to reproduce were:
			    	// 0) Open model with errors trace
			    	// 1) Drag the model editor on top of the TLC error view
			    	// 2) Change focus from model editor, to TLC error and spec editor a couple of times
			    	// 3) Run the model
			    	// 4) Cycle focus
					// 5) Bam!
					TLCErrorView.updateErrorView(config, !UIHelper.isInSameStack(editor, TLCErrorView.ID));
				} else {
					errorView.clear();
				}
			}
		}
    }

}
