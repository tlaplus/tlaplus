package org.lamport.tla.toolbox.editor.basic.handlers;

import java.util.ResourceBundle;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.ui.editors.text.IFoldingCommandIds;
import org.eclipse.ui.texteditor.TextOperationAction;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

/**
 * Expand all foldable regions in the editor in focus.
 */
public class ExpandAllRegionsHandler extends AbstractHandler {
	private static final String BUNDLE_NAME= "org.eclipse.jdt.internal.ui.actions.FoldingMessages";
	private static final ResourceBundle RESOURCE_BUNDLE= ResourceBundle.getBundle(BUNDLE_NAME);

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
        final TLAEditor editor = EditorUtil.getTLAEditorWithFocus();

		if (editor != null) {
			final TextOperationAction action = new TextOperationAction(RESOURCE_BUNDLE, "Projection.ExpandAll.", editor,
					ProjectionViewer.EXPAND_ALL, true);

			action.setActionDefinitionId(IFoldingCommandIds.FOLDING_EXPAND_ALL);
			action.run();
        }

        return null;
	}

}
