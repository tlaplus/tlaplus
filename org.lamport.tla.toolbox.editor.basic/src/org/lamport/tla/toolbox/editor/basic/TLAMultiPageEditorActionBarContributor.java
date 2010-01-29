package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IStatusLineManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.MultiPageEditorActionBarContributor;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.ITextEditorExtension;
import org.eclipse.ui.texteditor.RetargetTextEditorAction;
import org.eclipse.ui.texteditor.StatusLineContributionItem;

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
