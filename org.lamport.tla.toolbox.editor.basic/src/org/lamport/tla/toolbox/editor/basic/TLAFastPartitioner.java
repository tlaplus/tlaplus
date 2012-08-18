/*******************************************************************************
 * This file was created by Leslie Lamport in 2012 by modifying 
 * the file org.eclipse.jface.text.rules/FastPartitioner.  The latter file
 * contained the following copyright notice and contributor list.
 * 
 *    Copyright (c) 2000, 2006 IBM Corporation and others.
 *    All rights reserved. This program and the accompanying materials
 *    are made available under the terms of the Eclipse Public License v1.0
 *    which accompanies this distribution, and is available at
 *    http://www.eclipse.org/legal/epl-v10.html
 *
 *    Contributors:
 *        IBM Corporation - initial API and implementation
 *        
 * This class tokenizes an IDocument that represents a TLA+ spec that is being
 * edited in a module editor.  Tokenizing means partitioning the document by
 * adding to the IDocument object a collection of TypedPosition objects,
 * each describing a region of the document and a type, which is a string.  
 * Regions that lie between the regions specified by the TypedPosition
 * objects are considered to be regions of type IDocument.DEFAULT_CONTENT_TYPE.
 * The type is used to determine how text in that region should be colored.
 * 
 * The tokenization is performed by the TLAFastPartitioner object's methods calling
 * the appropriate methods of a TLAPartitionScanner object.  The key method is
 * the documentChanged method, which calls documentChanged2 to do the actual
 * work of re-tokenizing the document when it has changed.  That method in
 * turn calls TLAPartitionScanner.setPartialRange to set things up and then
 * issues a sequence of calls to TLAPartitionScanner.nextToken, which returns
 * the type of the region, each followed by calls to TLAPartitionScanner.getTokenLength
 * and TLAPartitionScanner.getTokenOffset to get the region's location (except
 * for regions of TLA code, which are represented by default regions with no
 * corresponding TypedPosition in the IDocument). 
 * 
 * This class also calls TLAPartitionScanner.setRange
 * 
 * That documentChanged2 method's argument is a DocumentEvent, which describes 
 * the change to the document as the replacement of a region of the original 
 * document with new text.  By examining the document's TypePosition objects 
 * for its old contents, the method tries to limit the amount of tokenization
 * that must be done using TLAPartitionScanner.  The way the method in the
 * original FastPartitioner class limits re-tokenization is based on the
 * assumption that the coloring of regions is done as in Java, where there is
 * a default region type (Java code) and other region types (comments and
 * strings) are completely independent of one another.    
 * 
 * To implement PlusCal shading with minimal changes to code I don't understand,
 * I added the following fields to this class.  (The value of all these fields 
 * is -1 if there is no PlusCal algorithm.)
 * 
 *    pcalStartCommentOffset 
 *       The offset of the partition for the MultiLineComment in which the
 *       PlusCal code is embedded.
 *       
 *    pcalStartOffset
 *       The offset of the partition containing the beginning of the PlusCal
 *       code.
 *       
 *    pcalStartLength 
 *       The length of the partition containing the beginning of the PlusCal
 *       code.
 *       
 *    pcalEndCommentOffset
 *       The offset of the MultiLineComment partition that follows the
 *       PlusCal algorithm.  (The text of that comment should be "*)".)
 *       Equals Integer.MAX_VALUE if the PlusCal code does not end.
 *       
 *    pcalEndCommentLength
 *       The length of the MultiLineComment partition that follows the
 *       PlusCal algorithm.  This should equal 2, but we add it as a
 *       separate field in case we decide to try to be more intelligent
 *       at finding the end of the algorithm and not use the comment-ending
 *       "*)".  Equals -1 if the PlusCal code does not end.
 *       
 * These are the values that these fields are set to after tokenization, so
 * the offsets are the ones for the old version of the document when
 * documentChanged2 is called.  Note that this allows only a single PlusCal
 * algorithm in a document.  It wouldn't be hard to change the code to 
 * allow multiple algorithms in a module, but since the translator looks
 * only at the first algorithm in the document, it seems best to color
 * only that one as a PlusCal algorithm.
 * 
 * TLAPartitionScanner.nextToken has been changed to return two additional
 * token types: PCalStartMultilineComment and PCalEndMultlineComment, which
 * represent the beginning and end of the multiline comment that contains
 * the algorithm.  (These tokens are converted to partitions of type
 * ordinary MultilineComment.)  All TLA tokens that TLAPartitionScanner.nextToken 
 * returns between those two tokens are converted to partiions of type PlusCal.
 * To allow nextToken to handle PlusCal algorithms, 
 * TLAPartitionScanner.setPartialRange has been changed to have an additional
 * argument that has three possible values:
 * 
 *   BEFORE_PCAL
 *      Means that scanning starts before any PlusCal algorithm (if there
 *      is any) in the document.  The scanner should therefore be looking for
 *      a MultiLineComment that contains "--fair" or "--algorithm".
 *      
 *   IN_PCAL
 *      It means that any part of the document not in a comment or string is
 *      PlusCal code--unless it is an unmatched "*)", which is a PlusCal ending
 *      comment.
 *      
 *   AFTER_PCAL
 *      It means that scanning is starting after the end of the PlusCal-ending
 *      MultiLineComment.  This means that the scanner should ignore any
 *      "--fair" or "--algorithm" in a MultiLineComment.
 *
 * In addition to this class and TLAPartitionScanner, the following classes 
 * have been modified to handle PlusCal algorithms:
 * 
 *    TLAReconcilingStrategy
 *    TLASourceViewerConfiguration
 *    TLAColorProvider  
 *    TLAEditorActivator
 *    TLAReconcilingStrategy
 *    TLASourceViewerConfiguration
 *    ITLAReserveredWords
 *    PCALCodeScanner (modified clone of TLACodeScanner)
 *******************************************************************************/
package org.lamport.tla.toolbox.editor.basic;


import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.Platform;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPositionCategoryException;
import org.eclipse.jface.text.DefaultPositionUpdater;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.DocumentRewriteSession;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.IDocumentPartitionerExtension;
import org.eclipse.jface.text.IDocumentPartitionerExtension2;
import org.eclipse.jface.text.IDocumentPartitionerExtension3;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.jface.text.TypedPosition;
import org.eclipse.jface.text.TypedRegion;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IToken;



/**
 * HERE IS THE DESCRIPTION OF THE ORIGINAL FastPartitioner CLASS:
 * 
 * A standard implementation of a document partitioner. It uses an
 * {@link IPartitionTokenScanner} to scan the document and to determine the
 * document's partitioning. The tokens returned by the scanner must return the
 * partition type as their data. The partitioner remembers the document's
 * partitions in the document itself rather than maintaining its own data
 * structure.
 * <p>
 * To reduce array creations in {@link IDocument#getPositions(String)}, the
 * positions get cached. The cache is cleared after updating the positions in
 * {@link #documentChanged2(DocumentEvent)}. Subclasses need to call
 * {@link #clearPositionCache()} after modifying the partitioner's positions.
 * The cached positions may be accessed through {@link #getPositions()}.
 * </p>
 *
 * @see IPartitionTokenScanner
 * @since 3.1
 */
public class TLAFastPartitioner implements IDocumentPartitioner, IDocumentPartitionerExtension, IDocumentPartitionerExtension2, IDocumentPartitionerExtension3 {

    /**
     * The position category this partitioner uses to store the document's partitioning information.
     */
    private static final String CONTENT_TYPES_CATEGORY= "__content_types_category"; //$NON-NLS-1$
    /** The partitioner's scanner */
    protected final TLAPartitionScanner fScanner;
    /** The legal content types of this partitioner */
    protected final String[] fLegalContentTypes;
    /** The partitioner's document */
    protected IDocument fDocument;
    /** The document length before a document change occurred */
    protected int fPreviousDocumentLength;
    /** The position updater used to for the default updating of partitions */
    protected final DefaultPositionUpdater fPositionUpdater;
    
    /** The offset at which the first changed partition starts */
    protected int fStartOffset;
    /** The offset at which the last changed partition ends */
    protected int fEndOffset;
    /**The offset at which a partition has been deleted
     * Added by LL on 14 Aug 2012:  This is the offset of the last partition examined
     * by documentChanged2 that was marked deleted by the call to 
     * fPositionUpdater.update(e) -- and hence I believe is the largest offset
     * of all such partitions.  Given this, I don't understand the definition how this 
     * value is used by createRegion, which computes the IRegion returned by documentChanged2.
     * 
     *  */
    protected int fDeleteOffset;
    
    /**
     * The position category this partitioner uses to store the document's partitioning information.
     * That is, it is a unique id generated when the TLAFastPartitioner object is created
     * under which this partitioner stores the information in the IDocument.
     */
    private final String fPositionCategory;
    
    /**
     * The active document rewrite session.
     */
    private DocumentRewriteSession fActiveRewriteSession;
    
    /**
     * Flag indicating whether this partitioner has been initialized.
     */
    private boolean fIsInitialized= false;
    
    /**
     * The cached positions from our document, so we don't create a new array every time
     * someone requests partition information.
     */
    private Position[] fCachedPositions= null;
    /** Debug option for cache consistency checking. */
    private static final boolean CHECK_CACHE_CONSISTENCY= "true".equalsIgnoreCase(Platform.getDebugOption("org.eclipse.jface.text/debug/FastPartitioner/PositionCache"));  //$NON-NLS-1$//$NON-NLS-2$;

    /*
     * The following five fields are described in the comments at the beginning
     * of this file.
     */
    private int pcalStartCommentOffset = -1 ;
    private int pcalStartOffset = -1 ;
    private int pcalStartLength = -1 ;
    private int pcalEndCommentOffset = -1 ;
    private int pcalEndCommentLength = -1 ;

    // Possible modes with which TLAPartitionScanner.setPartialRange can be called
    public static final int BEFORE_PCAL = 0 ;
    public static final int IN_PCAL     = 1 ;
    public static final int AFTER_PCAL  = 2 ;
    
    // The following are states used in deciding what to do with tokens
    // returned by calls to TLAPartitionScanner.nextToken.
    private static final int SEEK_ALGORITHM  = 0 ;
    private static final int START_ALGORITHM = 1 ;
    private static final int IN_ALGORITHM    = 2 ;
    private static final int AFTER_ALGORITHM = 3 ;

    /**
     * Creates a new partitioner that uses the given scanner and may return
     * partitions of the given legal content types.
     *
     * @param scanner the scanner this partitioner is supposed to use
     * @param legalContentTypes the legal content types of this partitioner
     */
    public TLAFastPartitioner(IPartitionTokenScanner scanner, String[] legalContentTypes) {
        fScanner= (TLAPartitionScanner) scanner;
        fLegalContentTypes= TextUtilities.copy(legalContentTypes);
        fPositionCategory= CONTENT_TYPES_CATEGORY + hashCode();
        fPositionUpdater= new DefaultPositionUpdater(fPositionCategory);
    }

    /*
     * @see org.eclipse.jface.text.IDocumentPartitionerExtension2#getManagingPositionCategories()
     */
    public String[] getManagingPositionCategories() {
        return new String[] { fPositionCategory };
    }

    /*
     * @see org.eclipse.jface.text.IDocumentPartitioner#connect(org.eclipse.jface.text.IDocument)
     */
    public final void connect(IDocument document) {
        connect(document, false);
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be extended by subclasses.
     * </p>
     */
    public void connect(IDocument document, boolean delayInitialization) {
        Assert.isNotNull(document);
        Assert.isTrue(!document.containsPositionCategory(fPositionCategory));

        fDocument= document;
        fDocument.addPositionCategory(fPositionCategory);

        fIsInitialized= false;
        if (!delayInitialization)
            checkInitialization();
    }

    /**
     * Calls {@link #initialize()} if the receiver is not yet initialized.
     */
    protected final void checkInitialization() {
        if (!fIsInitialized)
            initialize();
    }

    /**
     * Performs the initial partitioning of the partitioner's document.  It seems to be called
     * the first time a document is loaded during a Toolbox session.  It seems to get called 2-4 times,
     * each for a different TLAFastPartitioner object.  Fortunately, the documentChanged method
     * is called only once for each change.
     * 
     * <p>
     * May be extended by subclasses.
     * </p>
     */
    protected void initialize() {
        fIsInitialized= true;
        clearPositionCache();
        fScanner.setRange(fDocument, 0, fDocument.getLength());

        try {
            IToken token= fScanner.nextToken();
            while (!token.isEOF()) {

                String contentType= getTokenContentType(token);

                if (isSupportedContentType(contentType)) {
                    TypedPosition p= new TypedPosition(fScanner.getTokenOffset(), fScanner.getTokenLength(), contentType);
                    fDocument.addPosition(fPositionCategory, p);
                }

                token= fScanner.nextToken();
            }
        } catch (BadLocationException x) {
            // cannot happen as offsets come from scanner
        } catch (BadPositionCategoryException x) {
            // cannot happen if document has been connected before
        }
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be extended by subclasses.
     * </p>
     */
    public void disconnect() {

        Assert.isTrue(fDocument.containsPositionCategory(fPositionCategory));

        try {
            fDocument.removePositionCategory(fPositionCategory);
        } catch (BadPositionCategoryException x) {
            // can not happen because of Assert
        }
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be extended by subclasses.
     * </p>
     */
    public void documentAboutToBeChanged(DocumentEvent e) {
        if (fIsInitialized) {

            Assert.isTrue(e.getDocument() == fDocument);

            fPreviousDocumentLength= e.getDocument().getLength();
            fStartOffset= -1;
            fEndOffset= -1;
            fDeleteOffset= -1;
        }
    }

    /*
     * @see IDocumentPartitioner#documentChanged(DocumentEvent)
     */
    public final boolean documentChanged(DocumentEvent e) {
        if (fIsInitialized) {
            IRegion region= documentChanged2(e);
            return (region != null);
        }
        return false;
    }

    /**
     * Helper method for tracking the minimal region containing all partition changes.
     * If <code>offset</code> is smaller than the remembered offset, <code>offset</code>
     * will from now on be remembered. If <code>offset  + length</code> is greater than
     * the remembered end offset, it will be remembered from now on.
     *
     * @param offset the offset
     * @param length the length
     */
    private void rememberRegion(int offset, int length) {
        // remember start offset
        if (fStartOffset == -1)
            fStartOffset= offset;
        else if (offset < fStartOffset)
            fStartOffset= offset;

        // remember end offset
        int endOffset= offset + length;
        if (fEndOffset == -1)
            fEndOffset= endOffset;
        else if (endOffset > fEndOffset)
            fEndOffset= endOffset;
    }

    /**
     * Remembers the given offset as the deletion offset.
     *
     * @param offset the offset
     */
    private void rememberDeletedOffset(int offset) {
        fDeleteOffset= offset;
    }

    /**
     * Creates the minimal region containing all partition changes using the
     * remembered offset, end offset, and deletion offset.  This is the value
     * returned by documentChanged2.
     * 
     * Added by LL on 14 Aug 2012:  Given what the value of fDeleteOffset
     * equals, I don't understand its use in this method.  It seems that
     * one should remember both the largest and smallest offsets of 
     * deleted partitions and use them in the obvious way.
     *
     * @return the minimal region containing all the partition changes
     */
    private IRegion createRegion() {
        if (fDeleteOffset == -1) {
            if (fStartOffset == -1 || fEndOffset == -1)
                return null;
            return new Region(fStartOffset, fEndOffset - fStartOffset);
        } else if (fStartOffset == -1 || fEndOffset == -1) {
            return new Region(fDeleteOffset, 0);
        } else {
            int offset= Math.min(fDeleteOffset, fStartOffset);
            int endOffset= Math.max(fDeleteOffset, fEndOffset);
            return new Region(offset, endOffset - offset);
        }
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be extended by subclasses.
     * </p>
     */
    public IRegion documentChanged2(DocumentEvent e) {

        if (!fIsInitialized)
            return null;
        // debugPrint("Entering documentChanged2");
        try {
            Assert.isTrue(e.getDocument() == fDocument);

            // Set category to the array of all TypedPosition tokens
            // representing non-TLA partitions of the document.
            Position[] category= getPositions();
            
            // `reparseStart'  will be set to the location in the document
            // at which TLAPartitionScanner.nextToken will begin scanning.
            // We first set it to the beginning of the line in which
            // deletion/insertion begins.
            //
            IRegion line= fDocument.getLineInformationOfOffset(e.getOffset());
            int reparseStart= line.getOffset();
     
            // If `reparseStart' lies between the start of the MultilineComment 
            // that contains the PlusCal algorithm and the end of the PlusCal
            // partition containing the "--algorithm" or "--fair", then we set
            // it to the location at the beginning of that comment.
            //
            // If `reparseStart' lies between the start and end of the MultiLineComment
            // partition that ends the PlusCal algorithm, then we set it to the
            // start of that partition.
            //

            if (   (pcalStartOffset != -1) 
                && (reparseStart < pcalStartOffset + pcalStartLength)
                && (pcalStartCommentOffset < reparseStart)) {
              reparseStart = pcalStartCommentOffset ;
            }
            else if (   (pcalEndCommentOffset != -1) 
                     && (reparseStart < pcalEndCommentOffset + pcalEndCommentLength)
                     && (pcalEndCommentOffset < reparseStart)) {
              reparseStart = pcalEndCommentOffset ;              
            }

            int newLength= e.getText() == null ? 0 : e.getText().length();

            // We now set: 
            //
            //   - `reparseStart', `contentType', and `partitionOffset' to 
            //     the offset, token type, and partitionOffset arguments with 
            //     which TLAPartitionScanner.setPartialRange will be called.
            //
            //   - `first' to the index of the first partition in the array `category'
            //     corresponding to a partition in the old version of the document
            //     that will be retokenized.
            //
            // The following invariant is maintained:
            //
            //   /\ reparseStart \leq e.offset
            //   /\ \/ reparseStart is at the beginning of a line
            //      \/ reparseStart is at the beginning of a non-default partition
            //
            // This invariant ensures that reparseStart is never pointing at a position
            // in a MultiLineComment just to the right of something like "--algo".
            // 
            // IF first > 0 
            //   THEN position := position at index first-1
            //        IF position contains reparsestart 
            //          THEN partitionStart := position.offset
            //               contentType := position.type
            //               IF e.offset is the location just past partition
            //                 THEN (* This means that reparseStart < e.offset and  *)
            //                      (* is in the middle of a partition that could   *)
            //                      (* be extended by e.text                        *)
            //                      reparseStart := partition.offset
            //               first := first - 1;
            //        ELSIF reparseStart = e.offset = location just past partition
            //          THEN (* e.text could be a continuation of partition *)
            //               partitionStart := position.offset
            //               reparseStart    := position.offset
            //               contentType    := position.type
            //               first := first - 1
            //        ELSE   (* rparseStart is in the middle of a TLA/PlusCal region  *)
            //               (* and e.text will be inserted either into or at the end *)
            //               (* of this region, or else in the region produced by the *)
            //               (* token returned by nextToken() after it returns the    *)
            //               (* token for this TLA/PlusCal region.                    *)
            //               partitionStart := location just past partition
            //               contentType    := IDocument.DEFAULT_CONTENT_TYPE
            //               
            int partitionStart= -1;
            String contentType= null;
            int first= fDocument.computeIndexInCategory(fPositionCategory, reparseStart);
            if (first > 0)  {
                TypedPosition partition= (TypedPosition) category[first - 1];
                if (partition.includes(reparseStart)) {
                    partitionStart= partition.getOffset();
                    contentType= partition.getType();
                    if (e.getOffset() == partition.getOffset() + partition.getLength())
                        reparseStart= partitionStart;
                    -- first;
                } else if (reparseStart == e.getOffset() && reparseStart == partition.getOffset() + partition.getLength()) {
                    partitionStart= partition.getOffset();
                    contentType= partition.getType();
                    reparseStart= partitionStart;
                    -- first;
                } else {
                    partitionStart= partition.getOffset() + partition.getLength();
                    contentType= IDocument.DEFAULT_CONTENT_TYPE;
                }
            }
            
            // We now set pcalMode to the mode argument with which 
            // TLAPartitionScanner.setPartialRange is called to initialize the mode
            // in which scanning is begun.  We set it to
            //
            //    BEFORE_PCAL if there is no PlusCal algorithm or reparseStart is before
            //                the partition beginning with "--algorithm" or "--fair".
            //
            //    IN_PCAL     if reparseStart is between the partition beginning with
            //                "--algorithm" or "--fair" and the MultiLineComment token
            //                containing the "*)" that end the algorithm (if there is one).
            //
            //    AFTER_PCAL  If reparseStart is after the end of the algorithm.
            //
            // Remember that reparseStart \leq e.offset, so it represents the same location
            // in both the old and new versions of the document.
            //
            // We also set inPcal to be true iff pcalMode = IN_PCAL.  It will be true when
            // the next token of type TLA returned by TLAPartitionScanner.nextToken
            // is is actually a PlusCal token.
            //
            int pcalMode = BEFORE_PCAL ;
            if (   ((pcalStartOffset != -1) && (pcalStartOffset <= reparseStart))
                && (   (pcalEndCommentOffset == -1) 
                    || (reparseStart < pcalEndCommentOffset + pcalEndCommentLength))) {
                pcalMode = IN_PCAL ;
            }
            else if (   (pcalEndCommentOffset != -1) 
                     && (pcalEndCommentOffset + pcalEndCommentLength <= reparseStart)) {
                pcalMode = AFTER_PCAL ;
            }

            fPositionUpdater.update(e);
            for (int i= first; i < category.length; i++) {
                Position p= category[i];
                if (p.isDeleted) {
                    rememberDeletedOffset(e.getOffset());
                    break;
                }
            }
            
            // We now set category to the array of TypedPosition objects obtained from 
            // the ones for the old contents of the Document by modifying the positions
            // appropriately for ones that still correspond to regions in the new document,
            // and marking as deleted those corresponding to regions in the old document
            // that have been deleted.  
            clearPositionCache();
            category= getPositions();

            fScanner.setPartialRange(fDocument, reparseStart, fDocument.getLength() - reparseStart, 
                                     contentType, partitionStart, pcalMode);

            int behindLastScannedPosition= reparseStart;
            IToken token= fScanner.nextToken();

            /**
            * Delta is the amount by which locations in the old version of the
            * document lying past the changed region are moved to the
            * right in the new version.
            */
            int Delta = newLength - e.getLength() ;

            /**
            * prevPcal is true iff the old version of the document
            * had a PlusCal algorithm
            */
            boolean prevPcal = (pcalStartCommentOffset != -1) ;

            /***************************************************************
            * Set prevAfterPcal to the offset in the current version of    *
            * the document so that all offsets \geq prevAfterPcal lie in   *
            * regions that do not contain any part of a PlusCal algorithm  *
            * or its begin/end comments.                                   *
            *                                                              *
            * prevAfterPcal := IF prevPcal                                 
            *                    THEN IF pcalEndCommentOffset = -1         
            *                           THEN Infinity                      
            *                           ELSE LET tmp == pcalEndCommentOffset  
            *                                                + pcalEndCommentLength 
            *                                IN  IF e.offset \leq tmp THEN tmp + Delta 
            *                                                         ELSE tmp
            *                    ELSE 0                                 
            *                                                              *
            * Note that it's possible for some text after the location     *
            * prevAfterPcal to contain newly inserted text.  However,      *
            * that's not a problem because prevAfterPcal is used as a      *
            * minimum offset at which re-partitioning can stop in case     *
            * the original algorithm would stop before that point.  The    *
            * original algorithm should guarantee that repartitioning      *
            * does not stop until all the newly inserted text has been     *
            * partitioned.                                                 *
            ***************************************************************/
            int prevAfterPcal = 0 ;
            if (prevPcal) {
              if (pcalEndCommentOffset == -1) {
                  prevAfterPcal = Integer.MAX_VALUE ;
              }
              else {
                  int tmp = pcalEndCommentOffset + pcalEndCommentLength ;
                  if (e.getOffset() <= tmp) {
                      prevAfterPcal = tmp + Delta ;
                  }
                  else {
                      prevAfterPcal = tmp ;
                  }
              }
            }

            /***************************************************************
            * convert pcalStartCommentOffset, pcalStartOffset,             *
            * pcalEndCommentOffset to locations in the new document or -1  *
            * by calling convertOffset.  See the description of that       *
            * method                                                       *
            ***************************************************************/
            pcalStartCommentOffset = convertOffset(pcalStartCommentOffset, 
                                                   pcalStartOffset - pcalStartCommentOffset, 
                                                   e.getOffset(), e.getLength(), newLength) ;
            pcalStartOffset = convertOffset(pcalStartOffset, pcalStartLength,
                                            e.getOffset(), e.getLength(), newLength) ;
            pcalEndCommentOffset = convertOffset(pcalEndCommentOffset, pcalEndCommentLength,
                                   e.getOffset(), e.getLength(), newLength) ;

            /***************************************************************
            * The partioning is described in terms of states and           *
            * transitions, in which a token is obtained by calling         *
            * TLAPartitionScanner.nextToken and the action performed       *
            * depends on the type of token and the current state.  The     *
            * original algorithm from FastPartitioner stopped the          *
            * procedure when it had partitioned enough of the new version  *
            * of the document so that the later partitions that were       *
            * obtained by partitioning the previous version are still      *
            * valid.  To handle PlusCal, we have to sometimes keep         *
            * calling the nextToken routine longer than that.  The         *
            * variable canStop is true iff PlusCal processing does NOT     *
            * require extra calls of nextToken.                            *
            *                                                              *
            * Here is the initialization of the state and of canStop:      *
            *                                                              *
            * CASE pcalMode = BEFORE_PCAL                                  *
            *    canStop := \/ (~prevPCal)                                 *
            *               \/ /\ pcalStartCommentOffset # -1              *
            *                  /\ pcalStartOffset # -1                     *
            *               \/ current offSet \geq prevAfterPcal           *
            *    ---> SEEK_ALGORITHM                                       *
            *                                                              *
            * CASE pcalMode = AFTER_PCAL                                   *
            *    canStop := TRUE                                           *
            *    ---> AFTER_ALGORITHM                                      *
            *                                                              *
            * CASE pcalMode = IN_PCAL                                      *
            *    canStop := pcalEndCommentOffset # -1                      *
            *    --> IN_ALGORITHM                                          *
            *                                                              *
            ***************************************************************/
            int state ;
            boolean canStop ;
            if (pcalMode == BEFORE_PCAL) {
                canStop =    (! prevPcal)
                          || (   (pcalStartCommentOffset != -1)
                              && (pcalStartOffset != -1) )
                          || (reparseStart >= prevAfterPcal) ;
                state = SEEK_ALGORITHM ;   
            }
            else if (pcalMode == AFTER_PCAL) {
                canStop = true ;
                state = AFTER_ALGORITHM ;
            }
            else {
                canStop = (pcalEndCommentOffset != -1) ;
                state = IN_ALGORITHM ;
                
            }
            
            /***************************************************************
            * Here is the algorithm for handling tokens returned by        *
            * calling TLAPartitionScanner.nextToken.                       *
            *                                                              *
            * SEEK_ALGORITHM:                                              *
            *    Invariant: canStop = \/ (~prevPCal)                       *
            *                         \/ /\ pcalStartCommentOffset # -1    *
            *                            /\ pcalStartOffset # -1           *
            *                         \/ current offSet \geq prevAfterPcal *
            *     (PCalStartMultilineComment)                              *
            *        set pcalStartCommentOffset, pcalStartOffset           *
            *        convert token type to MultilineComment                *
            *        --> START_ALGORITHM                                   *
            *                                                              *
            *     (PCalEndMultilineComment) ERROR                          *
            *                                                              *
            *     (EOF) set pcalStartCommentOffset, pcalStartOffset,       *
            *               and pcalEndCommentOffset to -1                 *
            *     (OTHER)                                                  *
            *        canStop := \/ canStop                                 *
            *                   \/ current offSet \geq prevAfterPcal       *
            *        --> SEEK_ALGORITHM                                    *
            *                                                              *
            * START_ALGORITHM:                                             *
            *                                                              *
            *    (TLA)  set PcalStartLength                                *
            *           convert token type to PCal                         *
            *           canStop := pcalEndCommentOffset # -1               *
            *           --> IN_ALGORITHM                                   *
            *                                                              *
            *    (OTHER) ERROR                                             *
            *                                                              *
            * IN_ALGORITHM:                                                *
            *   Invariant: canStop = pcalEndCommentOffset # -1             *
            *                                                              *
            *   (TLA) convert token type to PCAL                           *
            *         --> IN_ALGORITHM                                     *
            *                                                              *
            *   (PCalEndMultilineComment)                                  *
            *       canStop := offSet \geq prevAfterPcal                   *
            *       set pcalEndCommentOffset, pcalEndCommentLength         *
            *       convert token type to MultiLineComment                 *
            *       inPCal := false                                        *
            *       ---> AFTER__ALGORITHM                                  *
            *                                                              *
            *   (PCalStartMultilineComment)  ERROR                         *
            *                                                              *
            *   (EOF)  pcalEndCommentOffset := -1                          *
            *          DONE                                                *
            *                                                              *
            *   (OTHER) --> IN_ALGORITHM                                   *
            *                                                              *
            * AFTER_ALGORITHM:                                             *
            *   Invariant: ~ canStop => current offSet < prevAfterPcal     *
            *                                                              *
            *   (PCalEndMultilineComment or PCalStartMultilineComment)     *
            *      ERROR                                                   *
            *                                                              *
            *   (EOF) DONE                                                 *
            *                                                              *
            *   (OTHER) canStop := \/ canStop                              *
            *                      \/ current offSet \geq prevAfterPcal    *
            *          --> AFTER_ALGORITHM                                 *
            ***************************************************************/
            while (!token.isEOF()) {

                contentType = getTokenContentType(token);

                if (!isSupportedContentType(contentType)) { 
                     if (   (state == IN_ALGORITHM)                    // Added for PlusCal 
                         || (state == START_ALGORITHM)) {              //  "
                         contentType = TLAPartitionScanner.TLA_PCAL ;  //  "
                     }                                                 //  "
                     else {                                            //  "
                    token= fScanner.nextToken();
                    continue;
                         }                                             //  "
                }

                int start= fScanner.getTokenOffset();
                int length= fScanner.getTokenLength();

                behindLastScannedPosition= start + length;
                int lastScannedPosition= behindLastScannedPosition - 1;
                
                // Execute the algorithm described above, except for converting
                // TLA tokens to PlusCal tokens which is done above, and for
                // actions taken upon the return of the EOF token, which are
                // done after the end of the enclosing while loop.
                //
                switch (state) {
                case SEEK_ALGORITHM:
                    if (contentType.equals(TLAPartitionScanner.TLA_START_PCAL_COMMENT)) {
                        pcalStartCommentOffset = start ;
                        pcalStartOffset = behindLastScannedPosition ;
                        contentType = TLAPartitionScanner.TLA_MULTI_LINE_COMMENT ;
                        state = START_ALGORITHM ;
                    }
                    else if (contentType.equals(TLAPartitionScanner.TLA_END_PCAL_COMMENT)) {
                        //ERROR
                        System.out.println("Error in TLAFastPartioner.documentChanged2: line 818") ;
                    }
                    else {
                        canStop = canStop || (behindLastScannedPosition >= prevAfterPcal);
                    }
                    break;
                case START_ALGORITHM:
                    pcalStartLength = length ;
                    canStop = (pcalEndCommentOffset != -1) ;
                    state = IN_ALGORITHM ;
                    if (pcalStartOffset != start) {
                        //ERROR
                        System.out.println("Error in TLAFastPartioner.documentChanged2: line 830") ;
                    }
                    if (! contentType.equals(TLAPartitionScanner.TLA_PCAL)) {
                        //ERROR
                        System.out.println("Error in TLAFastPartioner.documentChanged2: line 834") ;
                    }
                    break;
                case IN_ALGORITHM:
                    if (contentType.equals(TLAPartitionScanner.TLA_END_PCAL_COMMENT)) {
                        canStop = (behindLastScannedPosition >= prevAfterPcal);
                        pcalEndCommentOffset = start ;
                        pcalEndCommentLength = length ;
                        contentType = TLAPartitionScanner.TLA_MULTI_LINE_COMMENT ;
                        state = AFTER_ALGORITHM ;
                    }
                    else if (contentType.equals(TLAPartitionScanner.TLA_START_PCAL_COMMENT)) {
                        //ERROR
                        System.out.println("Error in TLAFastPartioner.documentChanged2: line 847") ;
                    }
                    break;
                case AFTER_ALGORITHM:
                    if (contentType.equals(TLAPartitionScanner.TLA_START_PCAL_COMMENT)
                        || contentType.equals(TLAPartitionScanner.TLA_END_PCAL_COMMENT)) {
                        //ERROR
                        System.out.println("Error in TLAFastPartioner.documentChanged2: line 854") ;
                    }
                    canStop = canStop || (behindLastScannedPosition >= prevAfterPcal) ;
                    break;
                default:
                    // ERROR
                    System.out.println("Error in TLAFastPartioner.documentChanged2: line 860") ;
                }

                // remove all affected positions.
                // 
                while (first < category.length) {
                    TypedPosition p= (TypedPosition) category[first];
                    if (lastScannedPosition >= p.offset + p.length ||
                            (p.overlapsWith(start, length) &&
                                (!fDocument.containsPosition(fPositionCategory, start, length) ||
                                 !contentType.equals(p.getType())))) {

                        rememberRegion(p.offset, p.length);
                        fDocument.removePosition(fPositionCategory, p);
                        ++ first;

                    } else
                        break;
                }

                // if position already exists and we have scanned at least the
                // area covered by the event, we are done
                if (fDocument.containsPosition(fPositionCategory, start, length)) {
                    if (   (lastScannedPosition >= e.getOffset() + newLength)
                        && canStop)  {                                                  // Added for PlusCal
                        // debugPrint("exit before EOF") ;
                        return createRegion();
                    }
                    ++ first;
                } else {
                    // insert the new type position
                    try {
                        fDocument.addPosition(fPositionCategory, new TypedPosition(start, length, contentType));
                        rememberRegion(start, length);
                    } catch (BadPositionCategoryException x) {
                    } catch (BadLocationException x) {
                    }
                }

                token= fScanner.nextToken();
            }

            // Actions for PlusCal processing done upon obtaining of an EOF token
            // from TLAPartitionScanner.nextToken
            switch (state) {
            case SEEK_ALGORITHM :
                pcalStartCommentOffset = -1 ;
                pcalStartOffset = -1 ;
                pcalEndCommentOffset = -1 ;
                break ;
            case START_ALGORITHM :
                System.out.println("Error in TLAFastPartioner.documentChanged2: line 917") ;
                break ;
            case IN_ALGORITHM :
                pcalEndCommentOffset = -1 ;
                break ;
            // nothing to do for the case AFTER_ALGORITHM.
            }
            
            first= fDocument.computeIndexInCategory(fPositionCategory, behindLastScannedPosition);

            clearPositionCache();
            category= getPositions();
            TypedPosition p;
            while (first < category.length) {
                p= (TypedPosition) category[first++];
                fDocument.removePosition(fPositionCategory, p);
                rememberRegion(p.offset, p.length);
            }

        } catch (BadPositionCategoryException x) {
            // should never happen on connected documents
        } catch (BadLocationException x) {
        } finally {
            clearPositionCache();
        }
        // debugPrint("exit after EOF") ;
        return createRegion();
    }

    /**
     * Returns the position in the partitoner's position category which is
     * close to the given offset. This is, the position has either an offset which
     * is the same as the given offset or an offset which is smaller than the given
     * offset. This method profits from the knowledge that a partitioning is
     * an ordered set of disjoint position.
     * <p>
     * May be extended or replaced by subclasses.
     * </p>
     * @param offset the offset for which to search the closest position
     * @return the closest position in the partitioner's category
     */
    protected TypedPosition findClosestPosition(int offset) {

        try {

            int index= fDocument.computeIndexInCategory(fPositionCategory, offset);
            Position[] category= getPositions();

            if (category.length == 0)
                return null;

            if (index < category.length) {
                if (offset == category[index].offset)
                    return (TypedPosition) category[index];
            }

            if (index > 0)
                index--;

            return (TypedPosition) category[index];

        } catch (BadPositionCategoryException x) {
        } catch (BadLocationException x) {
        }

        return null;
    }


    /**
     * {@inheritDoc}
     * <p>
     * May be replaced or extended by subclasses.
     * </p>
     */
    public String getContentType(int offset) {
        checkInitialization();

        TypedPosition p= findClosestPosition(offset);
        if (p != null && p.includes(offset))
            return p.getType();

        return IDocument.DEFAULT_CONTENT_TYPE;
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be replaced or extended by subclasses.
     * </p>
     */
    public ITypedRegion getPartition(int offset) {
        checkInitialization();

        try {

            Position[] category = getPositions();

            if (category == null || category.length == 0)
                return new TypedRegion(0, fDocument.getLength(), IDocument.DEFAULT_CONTENT_TYPE);

            int index= fDocument.computeIndexInCategory(fPositionCategory, offset);

            if (index < category.length) {

                TypedPosition next= (TypedPosition) category[index];

                if (offset == next.offset)
                    return new TypedRegion(next.getOffset(), next.getLength(), next.getType());

                if (index == 0)
                    return new TypedRegion(0, next.offset, IDocument.DEFAULT_CONTENT_TYPE);

                TypedPosition previous= (TypedPosition) category[index - 1];
                if (previous.includes(offset))
                    return new TypedRegion(previous.getOffset(), previous.getLength(), previous.getType());

                int endOffset= previous.getOffset() + previous.getLength();
                return new TypedRegion(endOffset, next.getOffset() - endOffset, IDocument.DEFAULT_CONTENT_TYPE);
            }

            TypedPosition previous= (TypedPosition) category[category.length - 1];
            if (previous.includes(offset))
                return new TypedRegion(previous.getOffset(), previous.getLength(), previous.getType());

            int endOffset= previous.getOffset() + previous.getLength();
            return new TypedRegion(endOffset, fDocument.getLength() - endOffset, IDocument.DEFAULT_CONTENT_TYPE);

        } catch (BadPositionCategoryException x) {
        } catch (BadLocationException x) {
        }

        return new TypedRegion(0, fDocument.getLength(), IDocument.DEFAULT_CONTENT_TYPE);
    }

    /**
     * Computes the offset in the new document corresponding to the offset of a region in the
     * old document starting at `offset' and having length `length'.   It is assumed that the 
     * new document is obtained from the old one by replacing text of length oldLength by 
     * text of length newLength at offset changeOffset.  However, if the specified region has been
     * changed, then the value returned is -1.
     * 
     * @param offset - the offset to be converted.
     * @param length - the length of the region starting at offset.
     * @param changeOffset - the offset of the changed region.
     * @param oldLength - the original length of the changed region.
     * @param newLength - the new length of the changed region.
     * @return
     */
    private final int convertOffset(int offset, int length, int changeOffset, int oldLength, int newLength) {
        if (offset + length <= changeOffset) {
            return offset ;
        }
        else if (changeOffset + oldLength <= offset) {
            return offset + newLength - oldLength ;
        }
        else {
            return -1 ;
        }
    }
    /*
     * @see IDocumentPartitioner#computePartitioning(int, int)
     */
    public final ITypedRegion[] computePartitioning(int offset, int length) {
        return computePartitioning(offset, length, false);
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be replaced or extended by subclasses.
     * </p>
     */
    public String[] getLegalContentTypes() {
        return TextUtilities.copy(fLegalContentTypes);
    }

    /**
     * Returns whether the given type is one of the legal content types.
     * <p>
     * May be extended by subclasses.
     * </p>
     *
     * @param contentType the content type to check
     * @return <code>true</code> if the content type is a legal content type
     */
    protected boolean isSupportedContentType(String contentType) {
        if (contentType != null) {
            for (int i= 0; i < fLegalContentTypes.length; i++) {
                if (fLegalContentTypes[i].equals(contentType))
                    return true;
            }
        }

        return false;
    }

    /**
     * Returns a content type encoded in the given token. If the token's
     * data is not <code>null</code> and a string it is assumed that
     * it is the encoded content type.
     * <p>
     * May be replaced or extended by subclasses.
     * </p>
     *
     * @param token the token whose content type is to be determined
     * @return the token's content type
     */
    protected String getTokenContentType(IToken token) {
        Object data= token.getData();
        if (data instanceof String)
            return (String) data;
        return null;
    }

    /* zero-length partition support */

    /**
     * {@inheritDoc}
     * <p>
     * May be replaced or extended by subclasses.
     * </p>
     */
    public String getContentType(int offset, boolean preferOpenPartitions) {
        return getPartition(offset, preferOpenPartitions).getType();
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be replaced or extended by subclasses.
     * </p>
     */
    public ITypedRegion getPartition(int offset, boolean preferOpenPartitions) {
        ITypedRegion region= getPartition(offset);
        if (preferOpenPartitions) {
            if (region.getOffset() == offset && !region.getType().equals(IDocument.DEFAULT_CONTENT_TYPE)) {
                if (offset > 0) {
                    region= getPartition(offset - 1);
                    if (region.getType().equals(IDocument.DEFAULT_CONTENT_TYPE))
                        return region;
                }
                return new TypedRegion(offset, 0, IDocument.DEFAULT_CONTENT_TYPE);
            }
        }
        return region;
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be replaced or extended by subclasses.
     * </p>
     */
    public ITypedRegion[] computePartitioning(int offset, int length, boolean includeZeroLengthPartitions) {
        checkInitialization();
        List list= new ArrayList();

        try {

            int endOffset= offset + length;

            Position[] category= getPositions();

            TypedPosition previous= null, current= null;
            int start, end, gapOffset;
            Position gap= new Position(0);

            int startIndex= getFirstIndexEndingAfterOffset(category, offset);
            int endIndex= getFirstIndexStartingAfterOffset(category, endOffset);
            for (int i= startIndex; i < endIndex; i++) {

                current= (TypedPosition) category[i];

                gapOffset= (previous != null) ? previous.getOffset() + previous.getLength() : 0;
                gap.setOffset(gapOffset);
                gap.setLength(current.getOffset() - gapOffset);
                if ((includeZeroLengthPartitions && overlapsOrTouches(gap, offset, length)) ||
                        (gap.getLength() > 0 && gap.overlapsWith(offset, length))) {
                    start= Math.max(offset, gapOffset);
                    end= Math.min(endOffset, gap.getOffset() + gap.getLength());
                    list.add(new TypedRegion(start, end - start, IDocument.DEFAULT_CONTENT_TYPE));
                }

                if (current.overlapsWith(offset, length)) {
                    start= Math.max(offset, current.getOffset());
                    end= Math.min(endOffset, current.getOffset() + current.getLength());
                    list.add(new TypedRegion(start, end - start, current.getType()));
                }

                previous= current;
            }

            if (previous != null) {
                gapOffset= previous.getOffset() + previous.getLength();
                gap.setOffset(gapOffset);
                gap.setLength(fDocument.getLength() - gapOffset);
                if ((includeZeroLengthPartitions && overlapsOrTouches(gap, offset, length)) ||
                        (gap.getLength() > 0 && gap.overlapsWith(offset, length))) {
                    start= Math.max(offset, gapOffset);
                    end= Math.min(endOffset, fDocument.getLength());
                    list.add(new TypedRegion(start, end - start, IDocument.DEFAULT_CONTENT_TYPE));
                }
            }

            if (list.isEmpty())
                list.add(new TypedRegion(offset, length, IDocument.DEFAULT_CONTENT_TYPE));

        } catch (BadPositionCategoryException ex) {
            // Make sure we clear the cache
            clearPositionCache();
        } catch (RuntimeException ex) {
            // Make sure we clear the cache
            clearPositionCache();
            throw ex;
        }

        TypedRegion[] result= new TypedRegion[list.size()];
        list.toArray(result);
        return result;
    }

    /**
     * Returns <code>true</code> if the given ranges overlap with or touch each other.
     *
     * @param gap the first range
     * @param offset the offset of the second range
     * @param length the length of the second range
     * @return <code>true</code> if the given ranges overlap with or touch each other
     */
    private boolean overlapsOrTouches(Position gap, int offset, int length) {
        return gap.getOffset() <= offset + length && offset <= gap.getOffset() + gap.getLength();
    }

    /**
     * Returns the index of the first position which ends after the given offset.
     *
     * @param positions the positions in linear order
     * @param offset the offset
     * @return the index of the first position which ends after the offset
     */
    private int getFirstIndexEndingAfterOffset(Position[] positions, int offset) {
        int i= -1, j= positions.length;
        while (j - i > 1) {
            int k= (i + j) >> 1;
            Position p= positions[k];
            if (p.getOffset() + p.getLength() > offset)
                j= k;
            else
                i= k;
        }
        return j;
    }

    /**
     * Returns the index of the first position which starts at or after the given offset.
     *
     * @param positions the positions in linear order
     * @param offset the offset
     * @return the index of the first position which starts after the offset
     */
    private int getFirstIndexStartingAfterOffset(Position[] positions, int offset) {
        int i= -1, j= positions.length;
        while (j - i > 1) {
            int k= (i + j) >> 1;
            Position p= positions[k];
            if (p.getOffset() >= offset)
                j= k;
            else
                i= k;
        }
        return j;
    }

    /*
     * @see org.eclipse.jface.text.IDocumentPartitionerExtension3#startRewriteSession(org.eclipse.jface.text.DocumentRewriteSession)
     */
    public void startRewriteSession(DocumentRewriteSession session) throws IllegalStateException {
        if (fActiveRewriteSession != null)
            throw new IllegalStateException();
        fActiveRewriteSession= session;
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be extended by subclasses.
     * </p>
     */
    public void stopRewriteSession(DocumentRewriteSession session) {
        if (fActiveRewriteSession == session)
            flushRewriteSession();
    }

    /**
     * {@inheritDoc}
     * <p>
     * May be extended by subclasses.
     * </p>
     */
    public DocumentRewriteSession getActiveRewriteSession() {
        return fActiveRewriteSession;
    }

    /**
     * Flushes the active rewrite session.
     */
    protected final void flushRewriteSession() {
        fActiveRewriteSession= null;

        // remove all position belonging to the partitioner position category
        try {
            fDocument.removePositionCategory(fPositionCategory);
        } catch (BadPositionCategoryException x) {
        }
        fDocument.addPositionCategory(fPositionCategory);

        fIsInitialized= false;
    }

    /**
     * Clears the position cache. Needs to be called whenever the positions have
     * been updated.
     */
    protected final void clearPositionCache() {
        if (fCachedPositions != null) {
            fCachedPositions= null;
        }
    }

    /**
     * Returns the partitioner's positions.   Apparently, this is an array of TypedPosition objects
     * that partitions the document, ordered from start to end.  These TypedPosition objects mark
     * all the non-TLA+ portions of the document--that is, comments, strings, and PlusCal tokens.
     *
     * @return the partitioner's positions
     * @throws BadPositionCategoryException if getting the positions from the
     *         document fails
     */
    protected final Position[] getPositions() throws BadPositionCategoryException {
        if (fCachedPositions == null) {
            fCachedPositions= fDocument.getPositions(fPositionCategory);
        } else if (CHECK_CACHE_CONSISTENCY) {
            Position[] positions= fDocument.getPositions(fPositionCategory);
            int len= Math.min(positions.length, fCachedPositions.length);
            for (int i= 0; i < len; i++) {
                if (!positions[i].equals(fCachedPositions[i]))
                    System.err.println("FastPartitioner.getPositions(): cached position is not up to date: from document: " + toString(positions[i]) + " in cache: " + toString(fCachedPositions[i])); //$NON-NLS-1$ //$NON-NLS-2$
            }
            for (int i= len; i < positions.length; i++)
                System.err.println("FastPartitioner.getPositions(): new position in document: " + toString(positions[i])); //$NON-NLS-1$
            for (int i= len; i < fCachedPositions.length; i++)
                System.err.println("FastPartitioner.getPositions(): stale position in cache: " + toString(fCachedPositions[i])); //$NON-NLS-1$
        }
        return fCachedPositions;
    }
    
    /**
     * For printing out debugging information
     *   (TypedPosition)
     * @param msg
     */
    public void debugPrint(String msg) {
        System.out.println("Debug print " + msg);
        System.out.println("Start comment offset: " + pcalStartCommentOffset
                + ";  Start: (" + pcalStartOffset + ", " + pcalStartLength + 
                ");  End comment: (" + pcalEndCommentOffset + ", "
                + pcalEndCommentLength + ")") ;
        Position[] positions = null;
        try {
            positions = fDocument.getPositions(fPositionCategory);
        } catch (BadPositionCategoryException e1) {
            System.out.println("Can't get positions") ;
            e1.printStackTrace();
            return ;
        }
        for (int i = 0; i < positions.length; i++) {
           try {
              TypedPosition position = (TypedPosition) positions[i] ;
              System.out.println("Position " + i + ": (" + position.getOffset()
                      + ", " + position.getLength() + ")  type: "
                      + position.getType() + (position.isDeleted?" DELETED":""));
              System.out.println("  `" + 
                      fDocument.get(position.getOffset(), position.getLength()) + "'") ;
        
           } catch (Exception e) {
                System.out.println("Item " + i + " Exception: " + e.getMessage()) ;
             }
        }
        IRegion result = createRegion();
        if (result == null) {
            System.out.println("Returned null");
        } else {
            System.out.println("Returned (" + result.getOffset() + ", " 
                + result.getLength() + ")") ;
        }
    }

    /**
     * Pretty print a <code>Position</code>.
     *
     * @param position the position to format
     * @return a formatted string
     */
    private String toString(Position position) {
        return "P[" + position.getOffset() + "+" + position.getLength() + "]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
    }
}
