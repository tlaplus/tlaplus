package org.lamport.tla.toolbox.editor.basic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

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
	private static final String BLOCK_COMMENT_DELIMITER_REGEX = "^[ \\t]*\\(\\*{3}\\**\\)\\s*$";
	
	private static final String PCAL_TRANSLATION_PREFIX_REGEX = "^\\\\\\*+ BEGIN TRANSLATION.*$";
	private static final String PCAL_TRANSLATION_SUFFIX_REGEX = "^\\\\\\*+ END TRANSLATION.*$";
	
	
    private IDocument document;
    /* the currently displayed projection annotations */
    protected final List<TLCProjectionAnnotation> currentAnnotations = new ArrayList<>();
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
			final HashMap<TLCProjectionAnnotation, Position> regionMap
													= determineFoldingRegions(partition, dirtyRegion, subRegion);
			final Annotation[] deletions;
			final HashMap<TLCProjectionAnnotation, Position> regionsToAdd = new HashMap<>();
			synchronized (currentAnnotations) {
				for (final Map.Entry<TLCProjectionAnnotation, Position> me : regionMap.entrySet()) {
					if (!currentAnnotations.remove(me.getKey())) {
						regionsToAdd.put(me.getKey(), me.getValue());
					}
				}
				
				deletions = currentAnnotations.toArray(new Annotation[currentAnnotations.size()]);
				currentAnnotations.clear();
				currentAnnotations.addAll(regionMap.keySet());
			}
			PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
				public void run() {
					editor.modifyProjectionAnnotations(deletions, regionsToAdd);
				}
			});
		}
	}
	
    /**
     * Once upon a time (the original version of this,) document partitioning was performed via
     * 	{@link IDocumentExtension3#computePartitioning(String, int, int, boolean)} and it did a
     * 	terrible job. Now, instead, we're using the Eclipse {@link FindReplaceDocumentAdapter} class.
     */
	private HashMap<TLCProjectionAnnotation, Position> determineFoldingRegions(final IRegion partition,
			final DirtyRegion dirtyRegion, final IRegion subRegion) {
    	// TODO use regions for tracking in optimizations on re-parses
//		final boolean isInitialParse = ((partition == null) && (dirtyRegion == null) && (subRegion == null));
		
		final HashMap<TLCProjectionAnnotation, Position> additions = new HashMap<>();

		// PCal location
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
					
					find = search.find(pcalStartLocation, "^\\*+\\)$", true, true, false, true);
					addProjectionAdditionToMap(additions, startLocation, find);
				}
			}
		} catch (final BadLocationException ble) { }
		
		
		// Translated PCal location
		try {
			IRegion find = search.find(0, PCAL_TRANSLATION_PREFIX_REGEX, true, true, false, true);
			
			if (find != null) {
				final int translationStartLocation = find.getOffset();
				
				find = search.find(translationStartLocation, PCAL_TRANSLATION_SUFFIX_REGEX, true, true, false, true);
				if (find != null) {
					addProjectionAdditionToMap(additions, translationStartLocation, find);
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
					addProjectionAdditionToMap(additions, lastFoundIndex, find);
				}
				
				inBlock = !inBlock;
				lastFoundIndex = find.getOffset();
				find = search.find((lastFoundIndex + find.getLength()), BLOCK_COMMENT_DELIMITER_REGEX, true, true, false, true);
			}
		} catch (final BadLocationException ble) { }
		
		return additions;
    }

	private void addProjectionAdditionToMap(final Map<TLCProjectionAnnotation, Position> additions, final int startLocation,
										    final IRegion find)
			throws BadLocationException {
		if (find != null) {
			final int endLocation = find.getOffset() + find.getLength();
			final int length = endLocation - startLocation;
			final int positionLength = length + ((document.getLength() > endLocation) ? 1 : 0);	// +1 to cover the newline
			final Position position = new Position(startLocation, positionLength);

			additions.put(new TLCProjectionAnnotation(document.get(startLocation, length)), position);
		}
	}
	
	
	// Nothing in the ProjectionAnnotation hierarchy implements equals/hashCode, we'd like such things to exist
	//		for reconciliation
	private static class TLCProjectionAnnotation extends ProjectionAnnotation {
		TLCProjectionAnnotation(final String text) {
			setText(text);
		}
		
		@Override
		public boolean equals(final Object other) {
			if (other == null) {
				return false;
			}
			
			if (!Annotation.class.isAssignableFrom(other.getClass())) {
				return false;
			}
			
			final Annotation otherAnnotation = (Annotation)other;
			final String otherText = otherAnnotation.getText();
			
			return Objects.equals(getText(), otherText);
		}
		
		@Override
		public int hashCode() {
			final String text = getText();
			
			if (text == null) {
				return 0;
			}
			
			return text.hashCode();
		}
	}
}
