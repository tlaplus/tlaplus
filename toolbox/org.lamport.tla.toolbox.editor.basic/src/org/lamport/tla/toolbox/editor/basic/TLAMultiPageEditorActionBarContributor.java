package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IStatusLineManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.editors.text.IFoldingCommandIds;
import org.eclipse.ui.part.MultiPageEditorActionBarContributor;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.ITextEditorExtension;
import org.eclipse.ui.texteditor.RetargetTextEditorAction;
import org.eclipse.ui.texteditor.StatusLineContributionItem;
import org.eclipse.ui.texteditor.TextOperationAction;

/**
 * This class can contribute actions to menus, toolbars, and coolbars, and 
 * status fields to the status line of the toolbox (status fields appear as items
 * at the bottom of the window such as the two numbers separated by a colon that given the line
 * and column of the cursor). This class can make contributions to those locations based on the
 * currently active editor.
 * 
 * This is currently used as the contributor class for the {@link TLAEditorAndPDFViewer}. Since that is
 * a multipage editor, this class must extend {@link MultiPageEditorActionBarContributor}. This is set as
 * the contributor class for {@link TLAEditorAndPDFViewer} in the extension that registers that class
 * as an editor.
 * 
 * This class currently contributes two actions to the edit menu:
 * 
 * 1.) A content assist item that brings up a list of suggestions for what to type relevant
 *     to the TLA and the position of the cursor.
 *     
 * 2.) A content tip item. I don't know what this does, but it was in the contributor class for the TLA editor
 *     before it was part of a multi page editor, so it is included in this class as well.
 *     
 * This class currently contributes one status field to the status line of the toolbox, the line and column
 * of the current cursor position, if the currently active editor is a text editor.
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAMultiPageEditorActionBarContributor extends MultiPageEditorActionBarContributor
{
    // currently active editor page
    private IEditorPart activeEditor;
    protected RetargetTextEditorAction fContentAssistProposal;
    protected RetargetTextEditorAction fContentAssistTip;
    protected TextOperationAction fFoldingExpand;
    protected TextOperationAction fFoldingExpandAll;
    protected TextOperationAction fFoldingCollapse;
    protected TextOperationAction fFoldingCollapseAll;
    // status field for the line and column of the cursor
    private StatusLineContributionItem cursorPositionStatusField;

    public TLAMultiPageEditorActionBarContributor()
    {
        super();
        fContentAssistProposal = new RetargetTextEditorAction(TLAEditorMessages.getResourceBundle(),
                "ContentAssistProposal."); //$NON-NLS-1$
        fContentAssistProposal.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_PROPOSALS);
        fContentAssistTip = new RetargetTextEditorAction(TLAEditorMessages.getResourceBundle(), "ContentAssistTip."); //$NON-NLS-1$
        fContentAssistTip.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_CONTEXT_INFORMATION);

        // status field for the line and column of the cursor
        cursorPositionStatusField = new StatusLineContributionItem(
                ITextEditorActionConstants.STATUS_CATEGORY_INPUT_POSITION);
    }

    /*
     * @see IEditorActionBarContributor#init(IActionBars)
     */
    public void init(IActionBars bars)
    {
        super.init(bars);

        IMenuManager menuManager = bars.getMenuManager();
        IMenuManager editMenu = menuManager.findMenuUsingPath("toolbox.edit.menu");
        if (editMenu != null)
        {
            editMenu.add(new Separator());
            editMenu.add(fContentAssistProposal);
            editMenu.add(fContentAssistTip);
        }
    }

    @Override
    public void setActivePage(IEditorPart activeEditor)
    {
        if (this.activeEditor == activeEditor)
        {
            return;
        }

        this.activeEditor = activeEditor;

        if (activeEditor instanceof ITextEditor)
        {
            // contribute the content assist and content tip actions for the active editor
            ITextEditor editor = (ITextEditor) activeEditor;
            fContentAssistProposal.setAction(editor.getAction("ContentAssistProposal")); //$NON-NLS-1$
            fContentAssistTip.setAction(editor.getAction("ContentAssistTip")); //$NON-NLS-1$

			// Make the current editor's undo/redo actions the actions that are executed
			// when a user clicks Edit > Undo or Redo in the menu bar.  Without this, the
            // undo (or redo) of the previous editor remains active, which means a user
            // click undoes a change in the non-active editor.  To reproduce the old,
            // broken behavior, a) comment the three lines below, b) open two editors
            // in the Toolbox, c) make a change in the active editor (let's call it A),
            // d) switch to the other editor B, e) click menu Edit > Undo, f) see how
            // the change in A gets undone.
            // Note that some recent change in Eclipse has caused this bug to surface:
            // https://bugs.eclipse.org/571513
            final IActionBars actionBars = getActionBars();
			actionBars.setGlobalActionHandler("undo", editor.getAction("undo"));
			actionBars.setGlobalActionHandler("redo", editor.getAction("redo"));
			
            // the following code registers the eclipse folding actions globally
            // so that keystrokes can be used for them
            if (fFoldingExpand == null)
            {
                fFoldingExpand = new TextOperationAction(TLAEditorMessages.getResourceBundle(), "Projection.Expand.",
                        editor, ProjectionViewer.EXPAND, true);
                fFoldingExpand.setActionDefinitionId(IFoldingCommandIds.FOLDING_EXPAND);
            } else
            {
                fFoldingExpand.setEditor(editor);
            }
            editor.setAction(IFoldingCommandIds.FOLDING_EXPAND, fFoldingExpand);
            getActionBars().getGlobalActionHandler(fFoldingExpand.getActionDefinitionId());

            if (fFoldingExpandAll == null)
            {
                fFoldingExpandAll = new TextOperationAction(TLAEditorMessages.getResourceBundle(),
                        "Projection.ExpandAll.", editor, ProjectionViewer.EXPAND_ALL, true);
                fFoldingExpandAll.setActionDefinitionId(IFoldingCommandIds.FOLDING_EXPAND_ALL);
            } else
            {
                fFoldingExpandAll.setEditor(editor);
            }
            editor.setAction(IFoldingCommandIds.FOLDING_EXPAND_ALL, fFoldingExpandAll);
            getActionBars().getGlobalActionHandler(fFoldingExpandAll.getActionDefinitionId());

            if (fFoldingCollapse == null)
            {
                fFoldingCollapse = new TextOperationAction(TLAEditorMessages.getResourceBundle(),
                        "Projection.Collapse.", editor, ProjectionViewer.COLLAPSE, true);
                fFoldingCollapse.setActionDefinitionId(IFoldingCommandIds.FOLDING_COLLAPSE);
            } else
            {
                fFoldingCollapse.setEditor(editor);
            }
            editor.setAction(IFoldingCommandIds.FOLDING_COLLAPSE, fFoldingCollapse);
            getActionBars().getGlobalActionHandler(fFoldingCollapse.getActionDefinitionId());

            if (fFoldingCollapseAll == null)
            {
                fFoldingCollapseAll = new TextOperationAction(TLAEditorMessages.getResourceBundle(),
                        "Projection.CollapseAll.", editor, ProjectionViewer.COLLAPSE_ALL, true);
                fFoldingCollapseAll.setActionDefinitionId(IFoldingCommandIds.FOLDING_COLLAPSE_ALL);
            } else
            {
                fFoldingCollapseAll.setEditor(editor);
            }
            editor.setAction(IFoldingCommandIds.FOLDING_COLLAPSE_ALL, fFoldingCollapseAll);
            getActionBars().getGlobalActionHandler(fFoldingCollapseAll.getActionDefinitionId());

            if (editor instanceof ITextEditorExtension)
            {
                // set the status field for the cursor position
                ITextEditorExtension extension = (ITextEditorExtension) editor;
                extension.setStatusField(cursorPositionStatusField,
                        ITextEditorActionConstants.STATUS_CATEGORY_INPUT_POSITION);
            }
        } else
        {
            fContentAssistProposal.setAction(null); //$NON-NLS-1$
            fContentAssistTip.setAction(null); //$NON-NLS-1$
        }

        // active editor may have changed, so update the status line
        contributeToStatusLine(getActionBars().getStatusLineManager());

    }

    public void contributeToStatusLine(IStatusLineManager statusLineManager)
    {
        if (this.activeEditor instanceof ITextEditor)
        {
            if (statusLineManager.find(cursorPositionStatusField.getId()) == null)
            {
                // add the cursor position if not already there
                statusLineManager.add(cursorPositionStatusField);
            }
        } else
        {
            // remove cursor position if the active editor is not a text editor
            statusLineManager.remove(cursorPositionStatusField);
        }
        // must update to show changes in UI
        statusLineManager.update(true);
    }

}
