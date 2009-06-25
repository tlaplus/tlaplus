package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.editors.text.TextEditorActionContributor;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.RetargetTextEditorAction;

/**
 * Content assist actions
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAEditorActionContributor extends TextEditorActionContributor
{

    protected RetargetTextEditorAction fContentAssistProposal;
    protected RetargetTextEditorAction fContentAssistTip;

    /**
     * Default constructor.
     */
    public TLAEditorActionContributor()
    {
        super();
        fContentAssistProposal = new RetargetTextEditorAction(TLAEditorMessages.getResourceBundle(),
                "ContentAssistProposal."); //$NON-NLS-1$
        fContentAssistProposal.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_PROPOSALS);
        fContentAssistTip = new RetargetTextEditorAction(TLAEditorMessages.getResourceBundle(), "ContentAssistTip."); //$NON-NLS-1$
        fContentAssistTip.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_CONTEXT_INFORMATION);
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

    /*
     * @see IEditorActionBarContributor#setActiveEditor(IEditorPart)
     */
    public void setActiveEditor(IEditorPart part)
    {
        super.setActiveEditor(part);
        ITextEditor editor = null;
        if (part instanceof ITextEditor) 
        {
            editor = (ITextEditor) part;
        }
        fContentAssistProposal.setAction(getAction(editor, "ContentAssistProposal")); //$NON-NLS-1$
        fContentAssistTip.setAction(getAction(editor, "ContentAssistTip")); //$NON-NLS-1$

    }

    /*
     * @see IEditorActionBarContributor#dispose()
     */
    public void dispose()
    {
        setActiveEditor(null);
        super.dispose();
    }
}
