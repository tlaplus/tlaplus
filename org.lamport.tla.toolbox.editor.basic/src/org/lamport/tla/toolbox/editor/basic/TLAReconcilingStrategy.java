package org.lamport.tla.toolbox.editor.basic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.reconciler.DirtyRegion;
import org.eclipse.jface.text.reconciler.IReconcilingStrategy;
import org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.editor.basic.pcal.IPCalReservedWords;

/**
 * We create this reconciling strategy for at least two reasons:
 * 	. having our custom source viewer configuration not use its super class' reconciler frees us from spell checking
 * 		markup
 * 	. to find fold locations for:
 * 			. block commments
 * 			. PlusCal code
 */
public class TLAReconcilingStrategy implements IReconcilingStrategy, IReconcilingStrategyExtension {
	// Per BoxedCommentHandler, a delimiter is "(" followed by three "*", then 0-N "*", and finally suffixed with ")"
	private static final String BLOCK_COMMENT_DELIMITER_REGEX = "^\\(\\*{3}\\**\\)$";
	
	
    private IDocument document;
    /* the currently displayed projection annotations */
    protected final List<ProjectionAnnotation> currentAnnotations = new ArrayList<>();
    /* the editor we're bound to */
    private TLAEditor editor;
	
    /**
     * {@inheritDoc}
     */
    @Override
	public void reconcile(final IRegion partition) {
    	reconcile(partition, null, null);
	}

    /**
     * {@inheritDoc}
     */
    @Override
	public void reconcile(final DirtyRegion dirtyRegion, final IRegion subRegion) {
    	reconcile(null, dirtyRegion, subRegion);
	}

    /**
     * {@inheritDoc}
     */
    @Override
	public void setDocument(final IDocument id) {
		document = id;
	}

    /**
     * {@inheritDoc}
     */
    @Override
	public void initialReconcile() {
    	reconcile(null, null, null);
	}

    /**
     * {@inheritDoc}
     */
    @Override
    public void setProgressMonitor(final IProgressMonitor monitor) { }

    /**
     * Sets the editor to which we're bound; this is required for communicating folding projections.
     * 
     * @param editor
     */
	public void setEditor(final TLAEditor tlaEditor) {
		editor = tlaEditor;
	}
	
	private void reconcile(final IRegion partition, final DirtyRegion dirtyRegion, final IRegion subRegion) {
		if (editor != null) {
			final HashMap<ProjectionAnnotation, Position> additions
													= determineFoldingRegions(partition, dirtyRegion, subRegion);
			PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
				public void run() {
					final Annotation[] deletions = currentAnnotations.toArray(new Annotation[currentAnnotations.size()]);
					editor.modifyProjectionAnnotations(deletions, additions);
					
					currentAnnotations.clear();
					currentAnnotations.addAll(additions.keySet());
				}
			});
		}
	}
	
    /**
     * Once upon a time (the original version of this,) document partitioning was performed via
     * 	{@link IDocumentExtension3#computePartitioning(String, int, int, boolean)} and it did a
     * 	terrible job. Now, instead, we're using the Eclipse {@link FindReplaceDocumentAdapter} class.
     */
	private HashMap<ProjectionAnnotation, Position> determineFoldingRegions(final IRegion partition,
			final DirtyRegion dirtyRegion, final IRegion subRegion) {
    	// TODO use regions for tracking in optimizations on re-parses
//		final boolean isInitialParse = ((partition == null) && (dirtyRegion == null) && (subRegion == null));
		
		final HashMap<ProjectionAnnotation, Position> additions = new HashMap<>();

		// PCAL locations
		final FindReplaceDocumentAdapter search = new FindReplaceDocumentAdapter(document);
		try {
			IRegion find = search.find(0, IPCalReservedWords.ALGORITHM, true, true, false, false);
			
			if (find == null) {
				find = search.find(0, "--" + IPCalReservedWords.FAIR, true, true, false, false);
			}
			
			if (find != null) {
				final int pcalStartLocation = find.getOffset();
				
				find = search.find(pcalStartLocation, "^\\(\\*", false, true, false, true);
				if (find != null) {
					final int startLocation = find.getOffset();
					
					find = search.find(pcalStartLocation, "\\*\\)$", true, true, false, true);
					addProjectAdditionToMap(additions, startLocation, find);
				}
			}
		} catch (final BadLocationException ble) { }
		
		
		// Block comment locations
		try {
			boolean inBlock = false;
			int lastFoundIndex = 0; // TODO future optimizations based on DocumentEvents' locations
			IRegion find = search.find(lastFoundIndex, BLOCK_COMMENT_DELIMITER_REGEX, true, true, false, true);
			
			while (find != null) {
				if (inBlock) {
					addProjectAdditionToMap(additions, lastFoundIndex, find);
				}
				
				inBlock = !inBlock;
				lastFoundIndex = find.getOffset();
				find = search.find((lastFoundIndex + find.getLength()), BLOCK_COMMENT_DELIMITER_REGEX, true, true, false, true);
			}
		} catch (final BadLocationException ble) { }
		
		return additions;
    }

	private void addProjectAdditionToMap(final Map<ProjectionAnnotation, Position> additions, final int startLocation,
										 final IRegion find)
			throws BadLocationException {
		if (find != null) {
			final int endLocation = find.getOffset() + find.getLength();
			final int length = endLocation - startLocation;
			final int positionLength = length + ((document.getLength() > endLocation) ? 1 : 0);	// +1 to cover the newline
			final Position position = new Position(startLocation, positionLength);
			final ProjectionAnnotation annotation = new ProjectionAnnotation();
			annotation.setText(document.get(startLocation, length));

			additions.put(annotation, position);
		}
	}
}
