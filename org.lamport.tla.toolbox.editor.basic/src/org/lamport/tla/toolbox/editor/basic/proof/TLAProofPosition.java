package org.lamport.tla.toolbox.editor.basic.proof;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.projection.IProjectionPosition;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;

import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;

/**
 * Represents a proof and its statement (step/theorem) for folding.
 * 
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAProofPosition extends Position implements IProjectionPosition
{

    /**
     * The {@link Position} of what the proof
     * attempts to prove. This could be the position
     * of a theorem, lemma, corollary, proof step, etc.
     */
    private Position positionOfProvable;
    /**
     * The {@link Position} of the proof.
     */
    private Position positionOfProof;
    /**
     * The fold annotation for this proof position.
     */
    private ProjectionAnnotation annotation;

    /**
     * For proof offset and length for a {@link ProofNode}, use {@link DocumentHelper#locationToRegion(IDocument, tla2sany.st.Location)}
     * for the location from {@link ProofNode#getLocation()}. For the offset and length of the provable, use the location
     * from {@link TheoremNode#getTheorem()} in the method {@link DocumentHelper#locationToRegion(IDocument, tla2sany.st.Location)}.
     * 
     * @param initProofOffset initial offset of the proof
     * @param initProofLength initial length of the proof
     * @param initProvableOffset initial offset of the statement of the theorem or step
     * for which this is a proof
     * @param initProvableLength initial length of the statement of the theorem or step
     * for which this is a proof
     * @param annotation {@link ProjectionAnnotation} that should be at this position
     * @param document
     */
    public TLAProofPosition(int initProofOffset, int initProofLength, int initProvableOffset, int initProvableLength,
            ProjectionAnnotation annotation, IDocument document)
    {
        // children = new Vector();
        /*
         * This seems to be a bit of a hack, but I see
         * no other way to do it correctly because of
         * how eclipse expands folds. In particular, when eclipse
         * is asked to expand a fold, it expands all lines between
         * the start line and end line, including the start line but
         * excluding the end line. It computes start
         * and end lines for a fold with offset and length in the following way:
         * 
         * start line: the greatest numbered line with
         *      first character offset <= offset of fold
         * 
         * end line: the greatest numbered line with
         *      first character offset <= offset + length of fold
         *      
         * In other words, it takes the offset of the fold and moves it back until it finds the start
         * of a line and takes the offset+length of a fold and moves it back until it finds the
         * start of a line. It then expands all lines in between and including those two lines. See
         * ProjectionViewer.addMasterDocumentRange() to see the exact implementation.
         * 
         * I think this is a silly way of doing things. The interface IProjectionPosition
         * allows the position to compute what lines are collapsed using the method
         * computeProjectionRegions but does not provide a way for the position to compute
         * what lines are expanded. This asymmetry can result in lines being collapsed
         * when a fold is collapsed but not re-expanded when the fold is expanded so that
         * lines just disappear. This requires being careful about the offset and length
         * of the position as well as what regions are collapsed.
         * 
         * The method alignRegion is stolen from the code for Java editor folding. Read the method
         * comments to see what it does. It should ensure that the entire proof is revealed
         * when expanded.
         */
        IRegion region = alignRegion(new Region(initProvableOffset, initProofOffset + initProofLength
                - initProvableOffset), document);
        if (region != null)
        {
            offset = region.getOffset();
            length = region.getLength();
        } else
        {
            // TODO something when position is one line
        }
        positionOfProvable = new Position(initProvableOffset, initProvableLength);
        positionOfProof = new Position(initProofOffset, initProofLength);
        this.annotation = annotation;

        // add positions to document so that they are updated on document changes.
        try
        {
            document.addPosition(positionOfProof);
            document.addPosition(positionOfProvable);
        } catch (BadLocationException e)
        {
            Activator.logError("Error installing positions for proof fold at " + this, e);
        }

    }

    public int computeCaptionOffset(IDocument document) throws BadLocationException
    {
        // TODO Auto-generated method stub
        return 0;
    }

    /**
     * Computes the regions that will be hidden when the fold at this
     * position is collapsed.
     */
    public IRegion[] computeProjectionRegions(IDocument document) throws BadLocationException
    {
        // fold all lines in the proof
        // that are not lines in the provable

        // first line in foldable region
        int firstLine = Math.max(document.getLineOfOffset(positionOfProvable.getOffset()
                + positionOfProvable.getLength()) + 1, document.getLineOfOffset(positionOfProof.getOffset()));

        // last line of proof
        int lastLine = document.getLineOfOffset(positionOfProof.getOffset() + positionOfProof.getLength());

        // If the last line is before the first line, then
        // the proof is on the same line as a line of the provable
        // so no regions should be folded.
        // We do not want any of the provable to be hidden when its
        // proof is folded.
        if (firstLine > lastLine)
        {
            // null indicates no folds
            return null;
        }

        int firstLineOffset = document.getLineOffset(firstLine);
        IRegion lastLineInfo = document.getLineInformation(lastLine);

        IRegion toFold = alignRegion(new Region(firstLineOffset, lastLineInfo.getOffset() + lastLineInfo.getLength()
                - firstLineOffset), document);

        if (toFold != null)
        {
            return new IRegion[] { toFold };
        }

        return null;
    }

    public ProjectionAnnotation getAnnotation()
    {
        return annotation;
    }

    /**
     * Returns whether or not this object represents
     * a foldable proof in the same position as proofRegion.
     * Considers only start and end lines, not characters.
     * 
     * @param proofRegion
     * @return
     * @throws BadLocationException 
     */
    public boolean isSamePosition(IRegion proofRegion, IDocument document) throws BadLocationException
    {
        return document.getLineOfOffset(positionOfProof.getOffset()) == document.getLineOfOffset(proofRegion
                .getOffset())
                && document.getLineOfOffset(positionOfProof.getOffset() + positionOfProof.getLength()) == document
                        .getLineOfOffset(proofRegion.getOffset() + proofRegion.getLength());
    }

    /**
     * Should be called when this is removed as a fold.
     * 
     * @param document from which this is being deleted
     */
    public void remove(IDocument document)
    {
        document.removePosition(positionOfProof);
        document.removePosition(positionOfProvable);
    }

    /**
     * Returns whether the offset is contained on any of the lines
     * of the proof or the statement. Note that this position ends
     * at the first offset of the line after the proof, but this method
     * does not consider that line part of the statement or the proof. The position
     * ends at that offset for reasons explained in the constructor of this class.
     * 
     * @return
     * @throws BadLocationException 
     */
    public boolean containsInProofOrStatement(int offset, IDocument document) throws BadLocationException
    {
        int startLine = document.getLineOfOffset(this.offset);
        /*
         *  Subtract 1 because this position ends
         *  at the first offset of the line after the proof, but this method
         *  does not consider that line part of the statement or the proof.
         */
        int endLine = document.getLineOfOffset(this.offset + length) - 1;

        int lineOfOffset = document.getLineOfOffset(offset);

        return lineOfOffset >= startLine && lineOfOffset <= endLine;
    }

    /**
     * Returns whether the offset is contained on any of the lines
     * of the proof. Note that this position ends
     * at the first offset of the line after the proof, but this method
     * does not consider that line part of the proof. The position
     * ends at that offset for reasons explained in the constructor of this class.
     * 
     * @param offset
     * @param document
     * @return
     * @throws BadLocationException 
     */
    public boolean containsInProof(int offset, IDocument document) throws BadLocationException
    {
        int startLine = document.getLineOfOffset(positionOfProof.getOffset());
        int endLine = document.getLineOfOffset(positionOfProof.getOffset() + positionOfProof.getLength());

        int lineOfOffset = document.getLineOfOffset(offset);

        return lineOfOffset >= startLine && lineOfOffset <= endLine;
    }

    /**
     * Returns whether the offset is contained on any of the lines
     * >= start line of the statement and < the start line of
     * the proof.
     * 
     * @param offset
     * @param document
     * @return
     * @throws BadLocationException 
     */
    public boolean containsBeforeProof(int offset, IDocument document) throws BadLocationException
    {
        int startLine = document.getLineOfOffset(positionOfProvable.getOffset());
        int endLine = document.getLineOfOffset(positionOfProof.getOffset());

        int lineOfOffset = document.getLineOfOffset(offset);

        return lineOfOffset >= startLine && lineOfOffset < endLine;
    }

    /**
     * Returns whether the input proofPosition is contained inside
     * this instance. More precisely, returns
     * 
     * this.offset <= proofPosition.getOffset() &&
     * this.offset + this.length >= proofPosition.getOffset() + proofPosition.getLength()
     * 
     * @param proofPosition
     * @return
     */
    public boolean contains(TLAProofPosition proofPosition)
    {
        return this.offset <= proofPosition.getOffset()
                && this.offset + this.length >= proofPosition.getOffset() + proofPosition.getLength();
    }

    /**
     * Aligns <code>region</code> to start and end at a line offset. The region's start is
     * decreased to the next line offset, and the end offset increased to the next line start or the
     * end of the document. <code>null</code> is returned if <code>region</code> is
     * <code>null</code> itself or if region's end line is less than its start line.
     *
     * @param region the region to align, may be <code>null</code>
     * @param document
     * @return a region equal or greater than <code>region</code> that is aligned with line
     *         offsets, <code>null</code> if the region is too small to be foldable (e.g. covers
     *         only one line)
     */
    protected final IRegion alignRegion(IRegion region, IDocument document)
    {
        if (region == null)
            return null;

        try
        {

            int start = document.getLineOfOffset(region.getOffset());
            int end = document.getLineOfOffset(region.getOffset() + region.getLength());
            if (start > end)
                return null;

            int offset = document.getLineOffset(start);
            int endOffset;
            if (document.getNumberOfLines() > end + 1)
                endOffset = document.getLineOffset(end + 1);
            else
                endOffset = document.getLineOffset(end) + document.getLineLength(end);

            return new Region(offset, endOffset - offset);

        } catch (BadLocationException x)
        {
            // concurrent modification
            return null;
        }
    }
}
