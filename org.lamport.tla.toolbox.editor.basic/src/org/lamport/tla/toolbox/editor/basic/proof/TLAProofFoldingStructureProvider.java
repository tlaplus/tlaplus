package org.lamport.tla.toolbox.editor.basic.proof;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.spec.parser.IParseResultListener;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.spec.parser.ParseResultBroadcaster;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import util.UniqueString;

/**
 * This class provides the foldable regions for the proofs
 * in a module.
 * 
 * Implementation note: currently, this class gets foldable information
 * from SANY. It gives the computed foldable positions to the eclipse folding
 * infrastructure. These positions are maintained by eclipse as sticky pointers
 * in the tla file. They are updated with each new successful parse by SANY.
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAProofFoldingStructureProvider implements IParseResultListener, IDocumentListener
{

    /**
     * Editor for which this class is providing proof folding
     * structure.
     */
    private TLAEditor editor;
    /**
     * The {@link IDocument} representing the
     * tla module.
     */
    private IDocument document;
    /**
     * List of all {@link TLAProofPosition} for the
     * current proofs in the editor most recently returned
     * by the parser.
     * 
     * Note that this does not include proofs whose
     * last line is the same of the last line
     * of the statement which they prove. These proofs
     * do not fold.
     */
    private Vector foldPositions;
    /**
     * Time stamp for last modification of the document
     * represented by the editor as returned by
     * {@link System#currentTimeMillis()}.
     */
    private long documentLastModified;
    /**
     * Flag indicating if folding commands
     * can be performed. This should be false
     * if the fold regions from a new parse result are being computed
     * and true if the fold regions are not being computed
     * and the fold regions in foldPositions are sorted
     * by offset.
     */
    private boolean canPerformFoldingCommands;

    /**
     * Initializes this folding structure provider for the given editor.
     * 
     * @param editor
     */
    public TLAProofFoldingStructureProvider(TLAEditor editor)
    {
        canPerformFoldingCommands = true;
        this.editor = editor;
        this.document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        foldPositions = new Vector();

        // add this as listener to document to listen for changes
        document.addDocumentListener(this);

        // get a parse result if the parse result broadcaster has already stored one
        ParseResult parseResult = ParseResultBroadcaster.getParseResultBroadcaster().getParseResult(
                ((FileEditorInput) editor.getEditorInput()).getFile().getLocation());

        if (parseResult != null)
        {
            newParseResult(parseResult);
        }

        // now listen to any new parse results
        ParseResultBroadcaster.getParseResultBroadcaster().addParseResultListener(this);

    }

    /**
     * Computes the {@link TLAProofPosition} for the {@link TheoremNode} and for any subproofs. For each proof in tree represented
     * by theoremNode, this determines if a matching fold exists in previousFolds. If one does exist, it is
     * removed from previous folds. If one does not exist, a new {@link TLAProofPosition} is created for the proof
     * and is added to additions.
     * 
     * Any {@link TLAProofPosition} that is added to additions or removed from previousFolds is added
     * to foldsInCurrentTree.
     * 
     * 
     * 
     * @param theoremNode
     * 
     * @throws BadLocationException 
     */
    private void computeProofFoldPositions(TheoremNode theoremNode, HashMap additions, List foldsInCurrentTree,
            List previousFolds) throws BadLocationException
    {

        if (theoremNode.getProof() == null)
        {
            return;
        }

        // the region describing the statement of the theorem
        IRegion theoremStatementRegion = AdapterFactory.locationToRegion(document, theoremNode.getTheorem()
                .getLocation());
        // the region describing the theoremNode
        IRegion theoremRegion = AdapterFactory.locationToRegion(document, theoremNode.getLocation());
        // the proof node
        ProofNode proofNode = theoremNode.getProof();
        // the region describing the proof
        IRegion proofNodeRegion = AdapterFactory.locationToRegion(document, proofNode.getLocation());

        // if last line of proof is on last line of step, nothing to fold, so just return
        if (document.getLineOfOffset(theoremStatementRegion.getOffset() + theoremStatementRegion.getLength()) == document
                .getLineOfOffset(proofNodeRegion.getOffset() + proofNodeRegion.getLength()))
        {
            return;
        }

        /* 
         * Iterate through previous folds to find if fold matches location of proof
         * 
         * If fold is found, remove from list of previous folds, and add to list of new folds for
         * proof tree.
         * 
         * If fold is not found, create new one, add to list of additions, and add to list of
         * new folds for proof tree.
         */
        TLAProofPosition matchingPosition = null;
        for (Iterator it = previousFolds.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();

            // positions are considered the same if the beginning and end line are the same
            if (proofPosition.isSamePosition(proofNodeRegion, document))
            {
                matchingPosition = proofPosition;
                foldsInCurrentTree.add(matchingPosition);
                // System.out.println("Existing fold found at " + matchingPosition);
                it.remove();
                break;
            }
        }

        if (matchingPosition == null)
        {
            /*
             * No position found.
             * 
             * Create a new positions whose statement part goes from the beginning of theoremNode
             * to the end of the statement of theoremNode.
             */
            matchingPosition = new TLAProofPosition(proofNodeRegion.getOffset(), proofNodeRegion.getLength(),
                    theoremRegion.getOffset(), theoremStatementRegion.getOffset() + theoremStatementRegion.getLength()
                            - theoremRegion.getOffset(), new ProjectionAnnotation(), document);
            additions.put(matchingPosition.getAnnotation(), matchingPosition);
            foldsInCurrentTree.add(matchingPosition);
        }

        if (proofNode instanceof NonLeafProofNode)
        {
            // recursively compute proof positions
            NonLeafProofNode nonLeafProofNode = (NonLeafProofNode) proofNode;
            LevelNode[] steps = nonLeafProofNode.getSteps();

            /*
             * From the documentation of NonLeafProofNode,
             * a step can be one of four types:
             * 
             * DefStepNode
             * UseOrHideNode
             * InstanceNode
             * TheoremNode
             * 
             * Only TheoremNode can have a proof. Recursively compute
             * the proof positions for those steps.
             */
            for (int i = 0; i < steps.length; i++)
            {
                if (steps[i] instanceof TheoremNode)
                {
                    computeProofFoldPositions((TheoremNode) steps[i], additions, foldsInCurrentTree, previousFolds);
                }
            }
        }

    }

    /**
     * Called when there is a new parse result broadcast by
     * {@link ParseResultBroadcaster}. Updates the folding structure of the proofs
     * in the editor.
     */
    public void newParseResult(ParseResult parseResult)
    {

        String moduleName = ResourceHelper.getModuleName(((FileEditorInput) editor.getEditorInput()).getFile());

        // System.out.println("Proof structure provider for " + moduleName + " recieved a parse result.");

        if (editor == null)
        {
            Activator.logDebug("Null editor in proof structure provider.");
            return;
        } else if (editor.getEditorInput() == null)
        {
            Activator.logDebug("Null editor input in proof structure provider.");
            return;
        }

        // check if the editor is dirty or the editor document has been modified
        // or saved before SANY finished
        // if it is, SANYs output is useless
        if (editor.isDirty()
                || parseResult.getParserCalled() < documentLastModified
                || parseResult.getParserCalled() < ((FileEditorInput) editor.getEditorInput()).getFile()
                        .getLocalTimeStamp())
        {
            return;
        }

        SpecObj specObj = parseResult.getSpecObj();

        if (specObj == null)
        {
            // module not successfully parsed
            return;
        }

        /*
         * Retrieve the ModuleNode corresponding to the module in the
         * editor.
         */
        Assert.isNotNull(specObj.getExternalModuleTable());

        ModuleNode moduleNode = specObj.getExternalModuleTable().getModuleNode(UniqueString.uniqueStringOf(moduleName));
        if (moduleNode == null)
        {
            // nothing to do
            return;
        }

        canPerformFoldingCommands = false;

        HashMap additions = new HashMap();
        Vector foldsInCurrentTree = new Vector();

        TheoremNode[] theorems = moduleNode.getTheorems();

        for (int i = 0; i < theorems.length; i++)
        {
            TheoremNode theoremNode = theorems[i];

            try
            {
                if (theoremNode.getLocation().source().equals(moduleName))
                {
                    /*TLAProofPosition theoremProof = */computeProofFoldPositions(theoremNode, additions,
                            foldsInCurrentTree, foldPositions);
                    // if (theoremProof != null)
                    // {
                    // rootPositions.add(theoremProof);
                    // }
                }
            } catch (BadLocationException e)
            {
                Activator.logError("Error converting theorem location to region in module " + moduleName, e);
            }
        }

        // compute array of annotations to be deleted
        Annotation[] deletions = new ProjectionAnnotation[foldPositions.size()];
        int i = 0;
        for (Iterator it = foldPositions.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();
            proofPosition.remove(document);
            deletions[i] = proofPosition.getAnnotation();
        }

        // set previous folds to new folds
        foldPositions = foldsInCurrentTree;

        editor.modifyProjectionAnnotations(deletions, additions, null);

        // check if foldPositions is sorted by offset
        // it probably is sorted, but in case the order returned by SANY changes,
        // then it makes sense to sort
        int currentOffset = -1;
        boolean isSorted = true;
        for (Iterator it = foldPositions.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();
            if (proofPosition.getOffset() >= currentOffset)
            {
                currentOffset = proofPosition.getOffset();
            } else
            {
                isSorted = false;
                break;
            }
        }

        if (!isSorted)
        {
            Collections.sort(foldPositions, new Comparator() {

                public int compare(Object arg0, Object arg1)
                {
                    if (arg0 instanceof TLAProofPosition && arg1 instanceof TLAProofPosition)
                    {
                        return ((TLAProofPosition) arg0).getOffset() - ((TLAProofPosition) arg1).getOffset();
                    } else
                    {
                        return 0;
                    }
                }
            });
        }

        canPerformFoldingCommands = true;

    }

    /**
     * Should be called when this instance is no longer needed.
     */
    public void dispose()
    {
        ParseResultBroadcaster.getParseResultBroadcaster().removeParseResultListener(this);
    }

    /**
     * This method used to assess whether the document has
     * changed between the time that the parser was called
     * and when it completes.
     */
    public void documentAboutToBeChanged(DocumentEvent event)
    {
        documentLastModified = System.currentTimeMillis();

    }

    public void documentChanged(DocumentEvent event)
    {

    }

    /**
     * Returns whether or not the selection is at a proof step or theorem statement.
     * The selection can be a range of text, so a selection
     * is considered to be at a proof step if the index in the document
     * described by {@link ITextSelection#getOffset()}+{@link ITextSelection#getLength()} is
     * in a step or theorem statement.
     * @param selection selection in the editor
     * @return
     */
    private boolean containedByStep(int caretOffset)
    {
        try
        {
            for (int i = 0; i < foldPositions.size(); i++)
            {
                TLAProofPosition proofPosition = (TLAProofPosition) foldPositions.get(i);
                if (proofPosition.containsBeforeProof(caretOffset, document))
                {
                    return true;
                }
            }
        } catch (BadLocationException e)
        {
            Activator.logError("Error computing if selection is in proof step.", e);
        }
        return false;
    }

    /**
     * Returns whether or not the selection is in a proof.
     * The selection can be a range of text, so a selection
     * is considered to be at a proof step if the index in the document
     * described by {@link ITextSelection#getOffset()}+{@link ITextSelection#getLength()} is
     * in a step or theorem statement.
     * @param selection selection in the editor
     * @return
     */
    private boolean containedByProof(int caretOffset)
    {
        try
        {
            for (int i = 0; i < foldPositions.size(); i++)
            {
                TLAProofPosition proofPosition = (TLAProofPosition) foldPositions.get(i);
                if (proofPosition.containsInProof(caretOffset, document))
                {
                    return true;
                }
            }
        } catch (BadLocationException e)
        {
            Activator.logError("Error computing if selection is in proof step.", e);
        }
        return false;
    }

    /**
     * Returns whether or not the selection is at a proof step, theorem statement, or leaf proof.
     * The selection can be a range of text, so a selection
     * is considered to be at a proof step if the index in the document
     * described by {@link ITextSelection#getOffset()}+{@link ITextSelection#getLength()} is
     * in a step or theorem statement.
     * @param selection selection in the editor
     * @return
     */
    private boolean containedByStepOrProof(int caretOffset)
    {
        try
        {
            for (int i = 0; i < foldPositions.size(); i++)
            {
                TLAProofPosition proofPosition = (TLAProofPosition) foldPositions.get(i);
                if (proofPosition.containsInProofOrStatement(caretOffset, document))
                {
                    return true;
                }
            }
        } catch (BadLocationException e)
        {
            Activator.logError("Error computing if selection is in proof step.", e);
        }
        return false;
    }

    /**
     * Returns whether the fold operation can be run. If this
     * returns false, then calling {@link TLAProofFoldingStructureProvider#runFoldOperation(String, ITextSelection)}
     * with the same commandId and caret offset should have no effect.
     * 
     * @param commandId
     * @param caretOffset
     * @return
     */
    public boolean canRunFoldOperation(String commandId, ITextSelection selection)
    {
        if (!canPerformFoldingCommands || selection == null)
        {
            return false;
        }

        int caretOffset = selection.getOffset() + selection.getLength();

        if (commandId.equals(IProofFoldCommandIds.FOCUS_ON_STEP))
        {
            // This can be done if the caret is at a step,
            // between a step and a proof (if there are empty lines
            // or comments in between a step and a proof), or at
            // a leaf proof.
            return containedByStepOrProof(caretOffset);
        } else if (commandId.equals(IProofFoldCommandIds.FOLD_ALL_PROOFS))
        {
            // Always possible.
            return true;
        } else if (commandId.equals(IProofFoldCommandIds.EXPAND_ALL_PROOFS))
        {
            // Always possible.
            return true;
        } else if (commandId.equals(IProofFoldCommandIds.EXPAND_SUBTREE))
        {
            // This can be done if the caret is at a step,
            // between a step and a proof (if there are empty lines
            // or comments in between a step and a proof).
            // This command does not make sense at a leaf proof.
            return containedByStep(caretOffset);
        } else if (commandId.equals(IProofFoldCommandIds.COLLAPSE_SUBTREE))
        {
            // This can be done if the caret is at a step,
            // between a step and a proof (if there are empty lines
            // or comments in between a step and a proof).
            // This command does not make sense at a leaf proof.
            return containedByStep(caretOffset);
        } else if (commandId.equals(IProofFoldCommandIds.SHOW_IMMEDIATE))
        {
            // This can be done if the caret is at a step,
            // between a step and a proof (if there are empty lines
            // or comments in between a step and a proof).
            // This command does not make sense at a leaf proof.
            return containedByStep(caretOffset);
        }
        return true;
    }

    /**
     * Runs the fold operation represented by commandId. This
     * should be an id from {@link IProofFoldCommandIds}.
     * 
     * Does nothing if currently computing the folds
     * from a parse result.
     * 
     * @param commandId
     * @param the current selection in the editor
     */
    public void runFoldOperation(String commandId, ITextSelection selection)
    {
        if (canPerformFoldingCommands)
        {
            /*
             * Allow commands to run even if a range of text
             * is selected (highlighted). We treat end of the selection
             * (indexed by offset+length) as the location of the caret
             * for the command. This means that for commands that act
             * on specific steps, the step on which the command acts is determined
             * by the position of selection.getOffset()+selection.getLength().
             */
            if (selection != null)
            {
                int caretOffset = selection.getOffset() + selection.getLength();
                if (commandId.equals(IProofFoldCommandIds.FOCUS_ON_STEP))
                {
                    foldEverythingUnusable(caretOffset);
                } else if (commandId.equals(IProofFoldCommandIds.FOLD_ALL_PROOFS))
                {
                    foldAllProofs();
                } else if (commandId.equals(IProofFoldCommandIds.EXPAND_ALL_PROOFS))
                {
                    expandAllProofs();
                } else if (commandId.equals(IProofFoldCommandIds.EXPAND_SUBTREE))
                {
                    expandCurrentSubtree(caretOffset);
                } else if (commandId.equals(IProofFoldCommandIds.COLLAPSE_SUBTREE))
                {
                    hideCurrentSubtree(caretOffset);
                } else if (commandId.equals(IProofFoldCommandIds.SHOW_IMMEDIATE))
                {
                    showImmediateDescendants(caretOffset);
                }
            }
        }
    }

    /**
     * Folds all proofs not containing the cursor.
     * 
     * Note that this will fold every proof if the cursor
     * is not in a proof.
     * 
     * @param cursorOffset
     */
    private void foldEverythingUnusable(int cursorOffset)
    {
        Vector modifiedAnnotations = new Vector();
        for (Iterator it = foldPositions.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();
            try
            {
                if (proofPosition.containsInProofOrStatement(cursorOffset, document))
                {
                    if (proofPosition.getAnnotation().isCollapsed())
                    {
                        proofPosition.getAnnotation().markExpanded();
                        modifiedAnnotations.add(proofPosition.getAnnotation());
                    }
                } else if (!proofPosition.getAnnotation().isCollapsed())
                {
                    proofPosition.getAnnotation().markCollapsed();
                    modifiedAnnotations.add(proofPosition.getAnnotation());
                }
            } catch (BadLocationException e)
            {
                Activator.logError("Error changing expansion state of proofs.", e);
            }
        }

        editor.modifyProjectionAnnotations(null, null, (Annotation[]) modifiedAnnotations
                .toArray(new ProjectionAnnotation[modifiedAnnotations.size()]));
    }

    /**
     * Collapses all proofs.
     * 
     * @param cursorOffset
     */
    private void foldAllProofs()
    {
        Vector modifiedAnnotations = new Vector();
        for (Iterator it = foldPositions.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();
            if (!proofPosition.getAnnotation().isCollapsed())
            {
                // should fold every proof
                // so that only theorem statements are shown
                proofPosition.getAnnotation().markCollapsed();
                modifiedAnnotations.add(proofPosition.getAnnotation());
            }
        }

        editor.modifyProjectionAnnotations(null, null, (Annotation[]) modifiedAnnotations
                .toArray(new ProjectionAnnotation[modifiedAnnotations.size()]));
    }

    private void expandAllProofs()
    {
        Vector modifiedAnnotations = new Vector();
        for (Iterator it = foldPositions.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();
            if (proofPosition.getAnnotation().isCollapsed())
            {
                // should fold every proof
                // so that only theorem statements are shown
                proofPosition.getAnnotation().markExpanded();
                modifiedAnnotations.add(proofPosition.getAnnotation());
            }
        }

        editor.modifyProjectionAnnotations(null, null, (Annotation[]) modifiedAnnotations
                .toArray(new ProjectionAnnotation[modifiedAnnotations.size()]));
    }

    /**
     * Expands the proof of a statement and all sub proofs. Assumes
     * all TLAProofPosition in foldPositions are sorted by ascending offset.
     */
    private void expandCurrentSubtree(int offset)
    {
        ArrayList modifiedAnnotations = new ArrayList();
        // find statement containing offset
        TLAProofPosition found = null;

        /*
         * Iterate though folds until finding the first
         * TLAProofPosition that contains the offset before
         * its proof (i.e. in the step/theorem or in a line
         * between the step/theorem and the proof). Expand the
         * proof of this TLAProofPosition and continue iterating, expanding
         * all proofs that are contained in the found TLAProofPosition.
         * 
         * This requires that the proof positions be sorted in ascending
         * order of offset.
         */
        for (Iterator it = foldPositions.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();
            try
            {
                if (found == null && proofPosition.containsBeforeProof(offset, document))
                {
                    found = proofPosition;
                    if (found.getAnnotation().isCollapsed())
                    {
                        found.getAnnotation().markExpanded();
                        modifiedAnnotations.add(found.getAnnotation());
                    }
                    continue;
                }

                if (found != null && found.contains(proofPosition))
                {
                    if (proofPosition.getAnnotation().isCollapsed())
                    {
                        proofPosition.getAnnotation().markExpanded();
                        modifiedAnnotations.add(proofPosition.getAnnotation());
                    }
                }
            } catch (BadLocationException e)
            {
                Activator.logError("Error changing expansion state of proofs.", e);
            }
        }

        editor.modifyProjectionAnnotations(null, null, (Annotation[]) modifiedAnnotations
                .toArray(new ProjectionAnnotation[modifiedAnnotations.size()]));
    }

    /**
     * Hides the proof of a statement and all subproofs. Assumes
     * all TLAProofPosition in foldPositions are sorted by ascending offset.
     */
    private void hideCurrentSubtree(int offset)
    {
        ArrayList modifiedAnnotations = new ArrayList();
        // find statement containing offset
        TLAProofPosition found = null;

        /*
         * Iterate though folds until finding the first
         * TLAProofPosition that contains the offset before
         * its proof (i.e. in the step/theorem or in a line
         * between the step/theorem and the proof). Collapse the
         * proof of this TLAProofPosition and continue iterating, collapsing
         * all proofs that are contained in the found TLAProofPosition.
         * 
         * This requires that the proof positions be sorted in ascending
         * order of offset.
         */
        for (Iterator it = foldPositions.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();
            try
            {
                if (found == null && proofPosition.containsBeforeProof(offset, document))
                {
                    found = proofPosition;
                    if (!found.getAnnotation().isCollapsed())
                    {
                        found.getAnnotation().markCollapsed();
                        modifiedAnnotations.add(found.getAnnotation());
                    }
                    continue;
                }

                if (found != null && found.contains(proofPosition))
                {
                    if (!proofPosition.getAnnotation().isCollapsed())
                    {
                        proofPosition.getAnnotation().markCollapsed();
                        modifiedAnnotations.add(proofPosition.getAnnotation());
                    }
                }
            } catch (BadLocationException e)
            {
                Activator.logError("Error changing expansion state of proofs.", e);
            }
        }

        editor.modifyProjectionAnnotations(null, null, (Annotation[]) modifiedAnnotations
                .toArray(new ProjectionAnnotation[modifiedAnnotations.size()]));
    }

    /**
     * Shows the immediate descendants in the proof of a
     * statement and hides the proofs of the immediate descendants.
     * Assumes all TLAProofPosition in foldPositions are sorted by ascending offset.
     */
    private void showImmediateDescendants(int offset)
    {
        ArrayList modifiedAnnotations = new ArrayList();
        // find statement containing offset
        TLAProofPosition found = null;

        /*
         * Iterate though folds until finding the first
         * TLAProofPosition that contains the offset before
         * its proof (i.e. in the step/theorem or in a line
         * between the step/theorem and the proof). Expand proof
         * of found statement and collapse the proofs of all
         * TLAProofPositions inside.
         * 
         * This requires that the proof positions be sorted in ascending
         * order of offset.
         */
        for (Iterator it = foldPositions.iterator(); it.hasNext();)
        {
            TLAProofPosition proofPosition = (TLAProofPosition) it.next();
            try
            {
                if (found == null && proofPosition.containsBeforeProof(offset, document))
                {
                    found = proofPosition;
                    if (found.getAnnotation().isCollapsed())
                    {
                        found.getAnnotation().markExpanded();
                        modifiedAnnotations.add(found.getAnnotation());
                    }
                    continue;
                }

                if (found != null && found.contains(proofPosition))
                {
                    if (!proofPosition.getAnnotation().isCollapsed())
                    {
                        proofPosition.getAnnotation().markCollapsed();
                        modifiedAnnotations.add(proofPosition.getAnnotation());
                    }
                }
            } catch (BadLocationException e)
            {
                Activator.logError("Error changing expansion state of proofs.", e);
            }
        }

        editor.modifyProjectionAnnotations(null, null, (Annotation[]) modifiedAnnotations
                .toArray(new ProjectionAnnotation[modifiedAnnotations.size()]));
    }

}
