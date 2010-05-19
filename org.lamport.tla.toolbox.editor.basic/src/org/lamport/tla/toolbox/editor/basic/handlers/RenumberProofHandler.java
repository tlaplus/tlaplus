/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import java.util.ArrayList;
import java.util.Arrays;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.widgets.Shell;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * @author lamport
 *
 */
public class RenumberProofHandler extends AbstractHandler implements IHandler
{
    private IDocument doc; // The document in the editor.
    private String text; // The document as a string.
    private ISelectionProvider selectionProvider; // 
    private TextSelection selection; // The current selection.
    private TheoremNode node; // The selected node
    private NonLeafProofNode pfNode;

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // Set the fields and return if we didn't get
        // a TheoremNode.
        if (!setFields())
        {
            return null;
        }

        // Get the names of the steps.

        try
        {
            Location stepLoc = null;
            LevelNode[] steps = pfNode.getSteps();

            // Set replace to the list of replacements.
            ArrayList replace = new ArrayList(15);
            int stepNumber = 1;
            for (int i = 0; i < steps.length; i++)
            {
                if (steps[i] instanceof TheoremNode)
                {
                    // check if the step has a leaf proof that uses <*>
                    // numbers, and abort if it does.
                    ProofNode stepPf = ((TheoremNode) steps[i]).getProof();
                    if ((stepPf != null) && (stepPf instanceof LeafProofNode))
                    {
                        Location leafPfLoc = stepPf.getLocation();
                        stepLoc = leafPfLoc;

                        IRegion ir = AdapterFactory.locationToRegion(doc, leafPfLoc);
                        String leafPfStr = doc.get(ir.getOffset(), ir.getLength());
                        if (leafPfStr.indexOf("<*>") > -1)
                        {
                            displayRenumberError("Cannot renumber proof that refers to <*> step numbers.");
                            return null;
                        }

                    }

                    // Get the step name.
                    UniqueString uname = ((TheoremNode) steps[i]).getName();
                    if (uname != null)
                    {
                        String oldName = uname.toString();
                        String newName = oldName.substring(0, oldName.indexOf('>') + 1) + stepNumber;
                        stepNumber++;
                        replace.add(new StringReplacement(oldName, newName));
                    }
                }
            }
            // Set replaceArray to the array of replacements, sorted in decreasing order
            // of oldString. This ensures that a replacement with oldString = s
            // appears in the list before a replacement having oldString a prefix of s.
            StringReplacement[] replaceArray = new StringReplacement[replace.size()];
            for (int i = 0; i < replaceArray.length; i++)
            {
                replaceArray[i] = (StringReplacement) replace.get(i);
            }
            Arrays.sort(replaceArray);

            // Set start/endRegion to the offsets delimiting the proof.
            IRegion pfRegion = AdapterFactory.locationToRegion(doc, pfNode.getLocation());
            int startRegion = pfRegion.getOffset();
            int endRegion = startRegion + pfRegion.getLength();

            // Set replacementOffsets to a list of IntPairs of the form <<os, rep>>
            // indicating that the replacement specified by replaceArray[rep] is to
            // be performed at offset os. They are sorted in order of increasing
            // offset.
            ArrayList replacementOffsets = new ArrayList(40);
            for (int i = 0; i < replaceArray.length; i++)
            {
                // Add to ArrayList the IntPairs for the replacements of
                // replaceArray[i].
                // searchFrom is the starting point for searching for next oldString
                // nextInsert is the next point in replacementOffsets to look
                // for a place to put the next replacement IntPair.
                int searchFrom = startRegion;
                int nextInsert = 0;
                boolean done = false;
                String oldString = replaceArray[i].oldStr;
                while (!done)
                {
                    int nextFound = text.indexOf(oldString, searchFrom);
                    if ((nextFound == -1) || !(nextFound < endRegion))
                    {
                        // No more instances of oldString.
                        done = true;
                    } else
                    {
                        // Found an instance of oldStr starting at nextFound
                        // Find the position in replacementOffsets to put the replacement.
                        while ((nextInsert < replacementOffsets.size())
                                && (((IntPair) replacementOffsets.get(nextInsert)).one < nextFound))
                        {
                            nextInsert++;
                        }
                        // We insert the replacement in replacementOffsets iff there is not already
                        // a replacement with the same offset (which must be for an old string of
                        // which the oldString is a prefix).
                        if ((nextInsert == replacementOffsets.size())
                                || (((IntPair) replacementOffsets.get(nextInsert)).one != nextFound))
                        {
                            replacementOffsets.add(nextInsert, new IntPair(nextFound, i));
                            nextInsert++;
                        }
                        searchFrom = nextFound + 1;
                    }
                }
            }

            // Do the replacements. We do them in reverse order so performing a
            // replacement doesn't change the offset of the following replacements.
            for (int i = replacementOffsets.size() - 1; i > -1; i--)
            {
                IntPair pair = (IntPair) replacementOffsets.get(i);
                StringReplacement rep = replaceArray[pair.two];
                doc.replace(pair.one, rep.oldStr.length(), rep.newStr);
            }

            // Test code to highlight region. Note method used to translate
            // a location to a region.
            // IRegion iregion = AdapterFactory.locationToRegion(doc, node.getLocation());
            // selectionProvider.setSelection(new TextSelection(iregion.getOffset(), pfRegion.getLength()));

        } catch (BadLocationException e)
        {

        }
        resetFields();
        return null;
    }

    /* Reprogram to disable or enable the command depending on whether the 
     * cursor is in a step that has a non-leaf proof.
     * (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#setEnabled(java.lang.Object)
     */
    public void setEnabled(Object context)
    {
        setBaseEnabled(setFields());
        resetFields();
    }

    /*
     * Sets the fields used by execute and setEnabled methods.  Returns false
     * iff it failed to set some field to a useful value;
     */
    private boolean setFields()
    {
        // The following code copied with minor modifications from BoxedCommentHandler
        TLAEditor editor;
        editor = EditorUtil.getTLAEditorWithFocus();
        // gets the editor to which command applies
        if (editor == null)
        {
            return false;
        }
        doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        text = doc.get();
        selectionProvider = editor.getSelectionProvider();
        selection = (TextSelection) selectionProvider.getSelection();
        node = EditorUtil.getCurrentTheoremNode();
        if (node == null)
        {
            return false;
        }
        ProofNode pf = node.getProof();
        if (pf instanceof NonLeafProofNode)
        {
            pfNode = (NonLeafProofNode) pf;
        } else
        {
            pfNode = null;
        }
        return true;
    }

    /*
     * Unsets the fields to save space.
     */
    private void resetFields()
    {
        doc = null;
        text = null;
        selectionProvider = null;
        selection = null;
        node = null;

    }

    void displayRenumberError(String msg)
    {
        Shell shell = UIHelper.getShellProvider().getShell();
        MessageDialog.openError(shell, "Renumbering Error", msg);
        resetFields();
        return;
    }

    /**
     * An object that contains two string fields, oldStr and newStr.
     * @author lamport
     *
     */
    private static class StringReplacement implements Comparable
    {
        String oldStr;
        String newStr;

        /**
         * The compareTo method compares the two old strings in the reverse
         * order, so sorting will sort them in inverse order.
         */
        public int compareTo(Object arg0)
        {
            return ((StringReplacement) arg0).oldStr.compareTo(this.oldStr);
        }

        StringReplacement(String o, String n)
        {
            oldStr = o;
            newStr = n;
        }

        public String toString()
        {
            return "`" + oldStr + "' -> `" + newStr + "'";
        }

    }

    private static class IntPair
    {
        int one;
        int two;

        IntPair(int o, int t)
        {
            one = o;
            two = t;
        }
    }
}
