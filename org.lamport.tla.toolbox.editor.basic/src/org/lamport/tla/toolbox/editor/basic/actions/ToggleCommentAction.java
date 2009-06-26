package org.lamport.tla.toolbox.editor.basic.actions;

import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.custom.BusyIndicator;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.ResourceAction;
import org.eclipse.ui.texteditor.TextEditorAction;
import org.lamport.tla.toolbox.editor.basic.TLAEditorMessages;

/**
 * This implementation has been copied from org.eclipse.jdt.internal.ui.javaeditor.ToggleCommentAction
 * (see org.eclipse.jdt.ui plugin)
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToggleCommentAction extends TextEditorAction
{
    public static final String COMMAND_ID = "toolbox.tla.editor.ToggleCommentAction";
    
    /** The text operation target */
    private ITextOperationTarget fOperationTarget;
    /** The document partitioning */
    private String fDocumentPartitioning;
    /** The comment prefixes */
    private Map fPrefixesMap;

    /**
     * Creates and initializes the action for the given text editor. The action
     * configures its visual representation from the given resource bundle.
     *
     * @param bundle the resource bundle
     * @param prefix a prefix to be prepended to the various resource keys
     *   (described in <code>ResourceAction</code> constructor), or
     *   <code>null</code> if none
     * @param editor the text editor
     * @see ResourceAction#ResourceAction(ResourceBundle, String, int)
     */
    public ToggleCommentAction(ResourceBundle bundle, String prefix, ITextEditor editor)
    {
        super(bundle, prefix, editor);
    }

    /**
     * Implementation of the <code>IAction</code> prototype. Checks if the selected
     * lines are all commented or not and uncomments/comments them respectively.
     */
    public void run()
    {
        if (fOperationTarget == null || fDocumentPartitioning == null || fPrefixesMap == null)
            return;

        ITextEditor editor = getTextEditor();
        if (editor == null)
            return;

        if (!validateEditorInputState())
            return;

        final int operationCode;
        if (isSelectionCommented(editor.getSelectionProvider().getSelection()))
            operationCode = ITextOperationTarget.STRIP_PREFIX;
        else
            operationCode = ITextOperationTarget.PREFIX;

        Shell shell = editor.getSite().getShell();
        if (!fOperationTarget.canDoOperation(operationCode))
        {
            if (shell != null)
                MessageDialog.openError(shell, TLAEditorMessages.getString("ToggleComment.error.title"),
                        TLAEditorMessages.getString("ToggleComment.error.message"));
            return;
        }

        Display display = null;
        if (shell != null && !shell.isDisposed())
            display = shell.getDisplay();

        BusyIndicator.showWhile(display, new Runnable() {
            public void run()
            {
                fOperationTarget.doOperation(operationCode);
            }
        });
    }

    /**
     * Is the given selection single-line commented?
     *
     * @param selection Selection to check
     * @return <code>true</code> iff all selected lines are commented
     */
    private boolean isSelectionCommented(ISelection selection)
    {
        if (!(selection instanceof ITextSelection))
            return false;

        ITextSelection textSelection = (ITextSelection) selection;
        if (textSelection.getStartLine() < 0 || textSelection.getEndLine() < 0)
            return false;

        IDocument document = getTextEditor().getDocumentProvider().getDocument(getTextEditor().getEditorInput());

        try
        {

            IRegion block = getTextBlockFromSelection(textSelection, document);
            ITypedRegion[] regions = TextUtilities.computePartitioning(document, fDocumentPartitioning, block
                    .getOffset(), block.getLength(), false);

            int lineCount = 0;
            int[] lines = new int[regions.length * 2]; // [startline, endline, startline, endline, ...]
            for (int i = 0, j = 0; i < regions.length; i++, j += 2)
            {
                // start line of region
                lines[j] = getFirstCompleteLineOfRegion(regions[i], document);
                // end line of region
                int length = regions[i].getLength();
                int offset = regions[i].getOffset() + length;
                if (length > 0)
                    offset--;
                lines[j + 1] = (lines[j] == -1 ? -1 : document.getLineOfOffset(offset));
                lineCount += lines[j + 1] - lines[j] + 1;
            }

            // Perform the check
            for (int i = 0, j = 0; i < regions.length; i++, j += 2)
            {
                String[] prefixes = (String[]) fPrefixesMap.get(regions[i].getType());
                if (prefixes != null && prefixes.length > 0 && lines[j] >= 0 && lines[j + 1] >= 0)
                    if (!isBlockCommented(lines[j], lines[j + 1], prefixes, document))
                        return false;
            }

            return true;

        } catch (BadLocationException x)
        {
            // should not happen
            // TODO
        }

        return false;
    }

    /**
     * Creates a region describing the text block (something that starts at
     * the beginning of a line) completely containing the current selection.
     *
     * @param selection The selection to use
     * @param document The document
     * @return the region describing the text block comprising the given selection
     */
    private IRegion getTextBlockFromSelection(ITextSelection selection, IDocument document)
    {

        try
        {
            IRegion line = document.getLineInformationOfOffset(selection.getOffset());
            int length = selection.getLength() == 0 ? line.getLength() : selection.getLength()
                    + (selection.getOffset() - line.getOffset());
            return new Region(line.getOffset(), length);

        } catch (BadLocationException x)
        {
            // should not happen
            // TODO
        }

        return null;
    }

    /**
     * Returns the index of the first line whose start offset is in the given text range.
     *
     * @param region the text range in characters where to find the line
     * @param document The document
     * @return the first line whose start index is in the given range, -1 if there is no such line
     */
    private int getFirstCompleteLineOfRegion(IRegion region, IDocument document)
    {

        try
        {

            int startLine = document.getLineOfOffset(region.getOffset());

            int offset = document.getLineOffset(startLine);
            if (offset >= region.getOffset())
                return startLine;

            offset = document.getLineOffset(startLine + 1);
            return (offset > region.getOffset() + region.getLength() ? -1 : startLine + 1);

        } catch (BadLocationException x)
        {
            // should not happen
            // TODO
        }

        return -1;
    }

    /**
     * Determines whether each line is prefixed by one of the prefixes.
     *
     * @param startLine Start line in document
     * @param endLine End line in document
     * @param prefixes Possible comment prefixes
     * @param document The document
     * @return <code>true</code> iff each line from <code>startLine</code>
     *             to and including <code>endLine</code> is prepended by one
     *             of the <code>prefixes</code>, ignoring whitespace at the
     *             begin of line
     */
    private boolean isBlockCommented(int startLine, int endLine, String[] prefixes, IDocument document)
    {

        try
        {

            // check for occurrences of prefixes in the given lines
            for (int i = startLine; i <= endLine; i++)
            {

                IRegion line = document.getLineInformation(i);
                String text = document.get(line.getOffset(), line.getLength());

                int[] found = TextUtilities.indexOf(prefixes, text, 0);

                if (found[0] == -1)
                    // found a line which is not commented
                    return false;

                String s = document.get(line.getOffset(), found[0]);
                s = s.trim();
                if (s.length() != 0)
                    // found a line which is not commented
                    return false;

            }

            return true;

        } catch (BadLocationException x)
        {
            // should not happen
            // TODO
        }

        return false;
    }

    /**
     * Implementation of the <code>IUpdate</code> prototype method discovers
     * the operation through the current editor's
     * <code>ITextOperationTarget</code> adapter, and sets the enabled state
     * accordingly.
     */
    public void update()
    {
        super.update();

        if (!canModifyEditor())
        {
            setEnabled(false);
            return;
        }

        ITextEditor editor = getTextEditor();
        if (fOperationTarget == null && editor != null)
            fOperationTarget = (ITextOperationTarget) editor.getAdapter(ITextOperationTarget.class);

        boolean isEnabled = (fOperationTarget != null && fOperationTarget.canDoOperation(ITextOperationTarget.PREFIX) && fOperationTarget
                .canDoOperation(ITextOperationTarget.STRIP_PREFIX));
        setEnabled(isEnabled);
    }

    /*
     * @see TextEditorAction#setEditor(ITextEditor)
     */
    public void setEditor(ITextEditor editor)
    {
        super.setEditor(editor);
        fOperationTarget = null;
    }

    /**
     * Configures the action
     * @param sourceViewer
     * @param configuration
     */
    public void configure(ISourceViewer sourceViewer, SourceViewerConfiguration configuration)
    {
        fPrefixesMap = null;

        String[] types = configuration.getConfiguredContentTypes(sourceViewer);
        Map prefixesMap = new HashMap(types.length);
        for (int i = 0; i < types.length; i++)
        {
            String type = types[i];
            String[] prefixes = configuration.getDefaultPrefixes(sourceViewer, type);
            if (prefixes != null && prefixes.length > 0)
            {
                int emptyPrefixes = 0;
                for (int j = 0; j < prefixes.length; j++)
                    if (prefixes[j].length() == 0)
                        emptyPrefixes++;

                if (emptyPrefixes > 0)
                {
                    String[] nonemptyPrefixes = new String[prefixes.length - emptyPrefixes];
                    for (int j = 0, k = 0; j < prefixes.length; j++)
                    {
                        String prefix = prefixes[j];
                        if (prefix.length() != 0)
                        {
                            nonemptyPrefixes[k] = prefix;
                            k++;
                        }
                    }
                    prefixes = nonemptyPrefixes;
                }

                prefixesMap.put(type, prefixes);
            }
        }
        fDocumentPartitioning = configuration.getConfiguredDocumentPartitioning(sourceViewer);
        fPrefixesMap = prefixesMap;
    }
}
