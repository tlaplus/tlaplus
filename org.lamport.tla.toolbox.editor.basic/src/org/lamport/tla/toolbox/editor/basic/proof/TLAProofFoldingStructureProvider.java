package org.lamport.tla.toolbox.editor.basic.proof;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.spec.parser.IParseResultListener;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.spec.parser.ParseResultBroadcaster;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.st.Location;
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
     * Collections of the proof trees of the module for which
     * this class is providing folding structure.
     * 
     * Each element of this collection is a tree whose root
     * is an instance of {@link Provable}.
     */
    private Vector proofTrees;
    /**
     * The {@link IDocument} representing the
     * tla module.
     */
    private IDocument document;
    /**
     * List of {@link IProof}'s in the current
     * proof trees.
     */
    // private Vector proofList;
    /**
     * List of {@link FoldTuple} for the current
     * proof trees.
     */
    private Vector folds;
    /**
     * Time stamp for last modification of the document
     * represented by the editor as returned by
     * {@link System#currentTimeMillis()}.
     */
    private long documentLastModified;

    /**
     * Initializes this folding structure provider for the given editor.
     * 
     * @param editor
     */
    public TLAProofFoldingStructureProvider(TLAEditor editor)
    {
        this.editor = editor;
        this.document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        proofTrees = new Vector();
        // proofList = new Vector();
        folds = new Vector();

        // add this as listener to document to listen for changes
        document.addDocumentListener(this);

        // get a parse result if the parse result broadcaster has already stored one
        ParseResult parseResult = ParseResultBroadcaster.getParseResultBroadcaster().getParseResult(
                ResourceHelper.getModuleName(((FileEditorInput) editor.getEditorInput()).getFile()));

        if (parseResult != null)
        {
            newParseResult(parseResult);
        }

        // now listen to any new parse results
        ParseResultBroadcaster.getParseResultBroadcaster().addParseResultListener(this);

    }

    /**
     * Computes all of the proof trees for the module.
     * 
     * Will do nothing if the spec status
     * is not "parsed" or if the editor is dirty. The current implementation
     * uses output from SANY to compute the proof trees, so if the editor is dirty
     * or the status is not "parsed" SANY's output is useless.
     */
    private void computeProofTrees(ModuleNode moduleNode)
    {
        proofTrees.clear();

        String moduleName = moduleNode.getName().toString();

        /*
         * Retrieve all theorems.
         */
        // its unclear if this method returns the theorems in inner modules
        // this needs to be tested
        TheoremNode[] theorems = moduleNode.getTheorems();

        // theorems includes theorems from extended modules
        // the proof trees for these theorems should not be computed

        /*
         * Convert SANY theorem data structure to the data structure
         * for this plug-in.
         */
        for (int i = 0; i < theorems.length; i++)
        {
            TheoremNode theoremNode = theorems[i];

            // DEBUGGING CODE
            try
            {

                // current position in the module of the theorem
                if (theoremNode.getLocation().source().equals(moduleName))
                {
                    IRegion region = DocumentHelper.locationToRegion(document, theoremNode.getLocation());
                    System.out.println("Theorem " + i + " : ");
                    System.out.println(document.get(region.getOffset(), region.getLength()));
                } else
                {
                    System.out.println("Found a theorem in module " + theoremNode.getLocation().source()
                            + ". Only looking for theorems in module " + moduleName + ".");
                }
            } catch (BadLocationException e)
            {

            }
            // END DEBUGGING CODE

            try
            {
                if (theoremNode.getLocation().source().equals(moduleName))
                {
                    IRegion theoremRegion = DocumentHelper.locationToRegion(document, theoremNode.getLocation());
                    Theorem theorem = new Theorem(theoremRegion.getOffset(), theoremRegion.getLength(), null);
                    ProofNode proofNode = theoremNode.getProof();
                    theorem.setProof(getProof(proofNode, theorem));

                    // add proof tree
                    proofTrees.add(theorem);
                }
            } catch (BadLocationException e)
            {
                Activator.logError("Error converting theorem location to region in module " + moduleName, e);
            }
        }
    }

    /**
     * Converts a {@link ProofNode} to an {@link IProof}.
     * 
     * @param proofNode
     * @param provable the {@link Provable} containing this proof
     * @return
     * @throws BadLocationException 
     */
    private Proof getProof(ProofNode proofNode, Provable provable) throws BadLocationException
    {
        // proofNode could be null in which case there is no proof for this theorem, so we are done
        if (proofNode != null)
        {

            IRegion proofNodeRegion = getProofRegion(document, proofNode.getLocation(), provable);
            // /*
            // * Search for previous proof that has same position and use annotation from that proof.
            // */
            // Iterator it = proofList.iterator();
            // ProjectionAnnotation proofAnnotation = null;
            // while (it.hasNext())
            // {
            // Proof proof = (Proof) it.next();
            // Position position = proof.getPosition();
            // if (position.getLength() == proofNodeRegion.getLength()
            // && position.getOffset() == proofNodeRegion.getOffset())
            // {
            // proofAnnotation = proof.getAnnotation();
            // }
            // }
            // if (proofAnnotation == null)
            // {
            // // no matching annotation
            // // create a new one
            // proofAnnotation = new ProjectionAnnotation();
            //
            // }

            if (proofNode instanceof LeafProofNode)
            {
                LeafProof leafProof = new LeafProof(proofNodeRegion.getOffset(), proofNodeRegion.getLength(), provable);
                return leafProof;
            } else
            {
                // should be instance of NonLeafProofNode
                NonLeafProofNode nonLeafProofNode = (NonLeafProofNode) proofNode;
                NonLeafProof nonLeafProof = new NonLeafProof(proofNodeRegion.getOffset(), proofNodeRegion.getLength(),
                        provable);
                LevelNode[] steps = nonLeafProofNode.getSteps();

                for (int i = 0; i < steps.length; i++)
                {
                    LevelNode step = steps[i];
                    Location stepLocation = step.getLocation();
                    IRegion stepRegion = DocumentHelper.locationToRegion(document, stepLocation);
                    Provable proofStep = new Provable(stepRegion.getOffset(), stepRegion.getLength(), provable);
                    nonLeafProof.addStep(proofStep);

                    /*
                     * From the documentation of NonLeafProofNode,
                     * a step can be one of four types:
                     * 
                     * DefStepNode
                     * UseOrHideNode
                     * InstanceNode
                     * TheoremNode
                     * 
                     * Only TheoremNode can have a proof.
                     */
                    if (step instanceof TheoremNode)
                    {
                        // step that potentially has a proof
                        TheoremNode provableStep = (TheoremNode) step;
                        proofStep.setProof(getProof(provableStep.getProof(), proofStep));

                        // TODO set the step number
                        // from the documentation for NonLeafProofNode, such a step
                        // is numbered iff getDef() returns a non-null value in which case *
                        // it is a ThmOrAssumpDefNode whose getName() field returns
                        // the step "number"
                    }

                }

                return nonLeafProof;
            }
        }
        return null;
    }

    /**
     * Called when there is a new parse result broadcast by
     * {@link ParseResultBroadcaster}.
     */
    public void newParseResult(ParseResult parseResult)
    {

        String moduleName = ResourceHelper.getModuleName(((FileEditorInput) editor.getEditorInput()).getFile());

        System.out.println("Proof structure provider for " + moduleName + " recieved a parse result.");

        if (editor == null)
        {
            Activator.logDebug("Null editor in proof structure provider.");
            return;
        } else if (editor.getEditorInput() == null)
        {
            Activator.logDebug("Null editor input in proof structure provider.");
            return;
        }

        // check if the editor is dirty
        // if it is, SANYs output is useless
        if (editor.isDirty()/*
                            || parseResult.getParserCalled() < documentLastModified
                            || parseResult.getParserCalled() < ((FileEditorInput) editor.getEditorInput()).getFile()
                            .getLocalTimeStamp()*/)
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

        computeProofTrees(moduleNode);

        Iterator it = proofTrees.iterator();

        // new folds to be added
        HashMap additions = new HashMap();

        // list of folds for the newly generated proof tree
        // that will be populated in the next while loop
        Vector newTreeFolds = new Vector();
        while (it.hasNext())
        {
            Theorem theorem = (Theorem) it.next();
            ProofTreeComponent[] components = theorem.getComponents();
            for (int i = 0; i < components.length; i++)
            {
                if (components[i] instanceof Proof)
                {
                    Proof proof = (Proof) components[i];
                    Position proofPosition = proof.getPosition();

                    /* 
                     * Iterate through previous folds to find if fold matches position of proof
                     * 
                     * If fold is found, bind to proof, remove from list of previous folds, and add to list of new folds for
                     * proof tree.
                     * 
                     * If fold is not found, create new one, bind to proof, add to list of additions, and add to list of
                     * new folds for proof tree.
                     * 
                     * The folds remaining in the list of previous folds after this while loop terminates are deleted.
                     */
                    Iterator previousFoldsIt = folds.iterator();
                    boolean foundExistingFold = false;
                    while (previousFoldsIt.hasNext())
                    {
                        FoldTuple fold = (FoldTuple) previousFoldsIt.next();
                        System.out.println("Previous fold at position " + fold.getPosition());
                        if (fold.getPosition().getOffset() == proofPosition.getOffset()
                                && fold.getPosition().getLength() == proofPosition.getLength())
                        {
                            System.out.println("Found existing fold at " + proofPosition + ". Fold is "
                                    + (fold.getAnnotation().isCollapsed() ? "collapsed." : "expanded."));
                            proof.setFold(fold);
                            previousFoldsIt.remove();
                            foundExistingFold = true;
                            newTreeFolds.add(fold);
                            break;
                        }
                    }

                    if (!foundExistingFold)
                    {
                        System.out.println("Creating new fold at position " + proofPosition);
                        FoldTuple newFold = new FoldTuple(new ProjectionAnnotation(), proofPosition);
                        proof.setFold(newFold);
                        additions.put(newFold.getAnnotation(), newFold.getPosition());
                        newTreeFolds.add(newFold);
                    }
                }
            }
        }

        // put the annotations remaining in the list of folds
        // into an array to be deleted
        ProjectionAnnotation[] deletions = new ProjectionAnnotation[folds.size()];
        for (int i = 0; i < deletions.length; i++)
        {
            deletions[i] = ((FoldTuple) folds.get(i)).getAnnotation();
        }

        folds = newTreeFolds;

        editor.modifyAnnotations(deletions, additions, null);
    }

    /**
     * Should be called when this instance is no longer needed.
     */
    public void dispose()
    {
        ParseResultBroadcaster.getParseResultBroadcaster().removeParseResultListener(this);
    }

    /**
     * 
     * @param document
     * @param location
     * @param provable
     * @return
     * @throws BadLocationException 
     */
    private IRegion getProofRegion(IDocument document, Location location, Provable provable)
            throws BadLocationException
    {
        /* The proof location that is returned by SANY is not necessarily the correct location of the fold
         * for that proof. When a proof is folded, we want the user to see none of the proof. However,
         * when eclipse folds a region, it shows the first line of that region. This code
         * compensates for that fact.
         * 
         * If the proof is not on the same line as the step it attempts to prove, then this code
         * expands the region describing the proof to include the last line of the step that it is trying
         * to prove.
         * 
         * If the proof is on the same line as the step then this method will return exactly the region described
         * by the location returned by SANY.
         */

        // region describing the location returned by SANY
        IRegion sanyRegion = DocumentHelper.locationToRegion(document, location);

        if (document.getLineOfOffset(sanyRegion.getOffset()) != document.getLineOfOffset(provable.getPosition()
                .getOffset()))
        {
            // // the first line of the region
            // int currentFirstLine = document.getLineOfOffset(sanyRegion.getOffset());
            // if (currentFirstLine > 0)
            // {
            // // new offset is beginning of the last line of the provable
            // int newOffset = document.getLineOffset(document.getLineOfOffset(provable.getPosition().getOffset()
            // + provable.getPosition().getLength()));
            // return new Region(newOffset, sanyRegion.getLength() + (sanyRegion.getOffset() - newOffset));
            // } else
            // {
            // // no previous line so do nothing
            // return sanyRegion;
            // }

            return DocumentHelper.getRegionWithPreviousLine(document, sanyRegion);
        }

        return sanyRegion;
    }

    public void documentAboutToBeChanged(DocumentEvent event)
    {
        documentLastModified = System.currentTimeMillis();

    }

    public void documentChanged(DocumentEvent event)
    {

    }

}
