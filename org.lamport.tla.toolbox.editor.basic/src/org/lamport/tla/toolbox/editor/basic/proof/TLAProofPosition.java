package org.lamport.tla.toolbox.editor.basic.proof;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DefaultPositionUpdater;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.projection.IProjectionPosition;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.AdapterFactory;

import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.st.Location;

/**
 * Represents a proof and its statement (step/theorem) for folding.
 * 
 * The offset and length of this class describe the region from the beginning
 * of the statement of the proof to the end of the proof. There are some
 * modifications done to the exact offset and length because
 * of the way in which eclipse displays, collapses, and expands folds. This
 * is explained in comments in the constructor for this class.
 * 
 * The method {@link TLAProofPosition#computeProjectionRegions(IDocument)} computes
 * the regions that will be collapsed when this is collapsed. See that method
 * for a description of what is collapsed.
 * 
 * Instances of this class also maintains the {@link Position} of the statement
 * and the {@link Position} of the proof. This can be used to determine if a certain
 * offset is contained specifically within the proof or within the statement. There
 * are methods in this class for computing this. These positions are also used
 * to compute the correct foldable regions.
 * 
 * Note that {@link Position}'s are added to a document to become sticky pointers
 * to locations. See {@link DefaultPositionUpdater} for the default implementation
 * of how sticky pointers are maintained for {@link Position}'s.
 * 
 * Note that the positions of the proof and statement are not interpretted by eclipse
 * in any way. Only the offset and length fields for this class (that are inherited
 * from {@link Position}) are used by eclipse to determine how the fold is displayed.
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
     * 
     * This position should span from the beginning
     * of the theorem or step (at <1>2 or THEOREM) to
     * the end of the statement of the step or theorem.
     */
    private Position positionOfStatement;
    /**
     * The {@link Position} of the proof.
     */
    private Position positionOfProof;
    /**
     * The fold annotation for this proof position.
     */
    private ProjectionAnnotation annotation;

    /**
     * Constructor for the position.
     * 
     * For the offset and length for the proof and statement, first obtain the {@link Location} from the syntax tree. For the proof, use
     * the location returned by {@link ProofNode#getLocation()}, where the {@link ProofNode} is obtained by {@link TheoremNode#getProof()}.
     * 
     * For initTheoremOffset, use the beginning of the location returned by {@link TheoremNode#getLocation()}.
     * 
     * For the end of the statement, use the end of the location returned by {@link LevelNode#getLocation()} 
     * for the {@link LevelNode} returned by {@link TheoremNode#getTheorem()}.
     *
     * To convert from the 4-int {@link Location} to the offset and length, use {@link AdapterFactory#locationToRegion(IDocument, Location)} and
     * then use the offset and length for the returned region.
     * 
     * @param initProofOffset initial offset of the proof
     * @param initProofLength initial length of the proof
     * @param initTheoremOffset initial offset of the theorem or step
     * for which this is a proof
     * @param initLengthToEndOfStatement initial length from initTheoremOffset to the end of
     * the statement of the theorem
     * @param annotation {@link ProjectionAnnotation} that should be at this position
     * @param document
     */
    public TLAProofPosition(int initProofOffset, int initProofLength, int initTheoremOffset,
            int initLengthToEndOfStatement, ProjectionAnnotation annotation, IDocument document)
    {
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
         * start of a line. It then expands all lines in between and including the start line but excluding
         * the end line. See ProjectionViewer.addMasterDocumentRange() to see the exact implementation.
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
        IRegion region = alignRegion(new Region(initTheoremOffset, initProofOffset + initProofLength
                - initTheoremOffset), document);

        offset = region.getOffset();
        length = region.getLength();

        positionOfStatement = new Position(initTheoremOffset, initLengthToEndOfStatement);
        positionOfProof = new Position(initProofOffset, initProofLength);
        this.annotation = annotation;

        // add positions to document so that they are updated on document changes.
        try
        {
            document.addPosition(positionOfProof);
            document.addPosition(positionOfStatement);
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
     * 
     * The following is from an email from Leslie. It starts by explaining
     * how comments should be used and folded in proofs and ends by describing
     * the folding rule.
     * 
     * In proofs, there are two
    ways I can think of for using comments:

    - At the beginning of a proof to explain the proof.  For example:

    <2>3. x > 0
      (********************************************************************)
      (* We prove y >0 and x \geq y by using Finagle's theorem and step   *)
      (* <1>3.                                                            *)
      (********************************************************************)
      <3>1. ...

    - As an informal leaf proof.  For example:

    <2>3. x > 0
     (*********************************************************************)
     (* This follows by simple algebra from <2>1 and <1>3, but I'm not    *)
     (* going to bother trying to convince this stupid prover that it     *)
     (* does.                                                             *)
     (*********************************************************************)

    <2>4. ...

    In this case, I will also want to add a PROOF OMITTED to tell
    the prover that I didn't just forget about this proof step.

    We can handle both these cases by the following rule, where the PROOF
    OMITTED follows the comment in the second case:

    When hiding a proof, hide everything from the (line following the)
    end of the statement being proved to the end of the proof.
     */
    public IRegion[] computeProjectionRegions(IDocument document) throws BadLocationException
    {

        /*
         * First line in foldable region - line following the end of the statement.
         */

        int firstLine = document.getLineOfOffset(positionOfStatement.getOffset() + positionOfStatement.getLength()) + 1;

        // last line of proof
        int lastLine = document.getLineOfOffset(positionOfProof.getOffset() + positionOfProof.getLength());

        // If the last line is before the first line, then
        // the proof is on the same line as a line of the statement
        // so no regions should be folded.
        // We do not want any of the statement to be hidden when its
        // proof is folded.
        if (firstLine > lastLine)
        {
            // null indicates no folds
            return null;
        }

        int firstLineOffset = document.getLineOffset(firstLine);
        IRegion lastLineInfo = document.getLineInformation(lastLine);

        /*
         * Eclipse does not allow for folding of single characters;
         * it only allows for line folding.
         * 
         * In particular, for each region r returned by this method,
         * eclipse will fold all lines line such that
         * 
         * line.offset >= r.offset && line.offset + line.length < r.offset + r.length
         * 
         * Notice that the second inequality is strictly less than. This forces
         * us to use the method alignRegion, stolen from the code used for Java
         * code folding and slightly modified.
         */
        IRegion toFold = alignRegion(new Region(firstLineOffset, lastLineInfo.getOffset() + lastLineInfo.getLength()
                - firstLineOffset), document);

        /*
         * The following line of code expands the position so that it ends at the end of the
         * region being collapsed. If this wasn't done then it would be possible to create
         * a situation in which a region that extends past the end of this position
         * is collapsed. When the fold for this position is expanded, not all of
         * it would be shown.
         * 
         * If the following line of code were removed, the following scenario
         * would create disappearing text. Place the caret at the beginning of the
         * line after a fold. Delete one character. Collapse the fold. Try to expand
         * the fold. All of the text in the fold will not reappear.
         * 
         * This is necessary because of the way in which eclipse expands folds.
         * Read the comment in the constructor to understand how eclipse
         * expands folds.
         */
        length = toFold.getOffset() + toFold.getLength() - offset;

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
     * Slightly more precisely, it returns true
     * if proofRegion starts and ends on the same line as the
     * {@link Position} representing the proof in this instance
     * of {@link TLAProofPosition}.
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
        document.removePosition(positionOfStatement);
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
        int startLine = document.getLineOfOffset(positionOfStatement.getOffset());
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
