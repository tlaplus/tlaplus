package org.lamport.tla.toolbox.editor.basic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.preference.IPreferenceStore;
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
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.editor.basic.pcal.IPCalReservedWords;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * We create this reconciling strategy for at least two reasons:
 * 	. having our custom source viewer configuration not use its super class' reconciler frees us from spell checking
 * 		markup
 * 	. to find fold locations for:
 * 			. block commments
 * 			. PlusCal code
 */
public class TLAReconcilingStrategy implements IPropertyChangeListener, IReconcilingStrategy, IReconcilingStrategyExtension {
	// Per BoxedCommentHandler, a delimiter is "(" followed by three "*", then 0-N "*", and finally suffixed with ")"
	private static final String BLOCK_COMMENT_DELIMITER_REGEX = "^[ \\t]*\\(\\*{3}\\**\\)\\s*$";
	// 
	private static final String SINGLE_LINE_COMMENT = "^[ \\t]*\\\\\\*";
	
	private static final String PCAL_TRANSLATION_PREFIX_REGEX = "^\\\\\\*+ BEGIN TRANSLATION.*$";
	private static final String PCAL_TRANSLATION_SUFFIX_REGEX = "^\\\\\\*+ END TRANSLATION.*$";
	
	
    private IDocument document;
    /* the currently displayed projection annotations */
    protected final List<TLCProjectionAnnotation> currentAnnotations;
    /* the editor we're bound to */
    private TLAEditor editor;
    /* the underlying source viewer */
    private ProjectionViewer projectionViewer;
    
    private final AtomicBoolean foldBlockComments;
    private final AtomicBoolean foldPlusCalAlgorithm;
    private final AtomicBoolean foldTranslatedPlusCalBlock;
	
    public TLAReconcilingStrategy() {
        final IPreferenceStore store = PreferenceStoreHelper.getInstancePreferenceStore();

        store.addPropertyChangeListener(this);
        
        currentAnnotations = new ArrayList<>();
        
        foldBlockComments = new AtomicBoolean(store.getBoolean(IPreferenceConstants.I_FOLDING_BLOCK_COMMENTS));
        foldPlusCalAlgorithm = new AtomicBoolean(store.getBoolean(IPreferenceConstants.I_FOLDING_PCAL_ALGORITHM));
        foldTranslatedPlusCalBlock = new AtomicBoolean(store.getBoolean(IPreferenceConstants.I_FOLDING_PCAL_TRANSLATED));
    }
    
    public void dispose() {
        final IPreferenceStore store = PreferenceStoreHelper.getInstancePreferenceStore();
        store.removePropertyChangeListener(this);
    }
    
	/**
     * {@inheritDoc}
     */
    @Override
	public void propertyChange(final PropertyChangeEvent event) {
    	final boolean reconcile;
    	
		if (IPreferenceConstants.I_FOLDING_BLOCK_COMMENTS.equals(event.getProperty())) {
			foldBlockComments.set(((Boolean)event.getNewValue()).booleanValue());
			reconcile = true;
		} else if (IPreferenceConstants.I_FOLDING_PCAL_ALGORITHM.equals(event.getProperty())) {
			foldPlusCalAlgorithm.set(((Boolean)event.getNewValue()).booleanValue());
			reconcile = true;
		} else if (IPreferenceConstants.I_FOLDING_PCAL_TRANSLATED.equals(event.getProperty())) {
			foldTranslatedPlusCalBlock.set(((Boolean)event.getNewValue()).booleanValue());
			reconcile = true;
		} else {
			reconcile = false;
		}
		
		if (reconcile) {
			reconcile(null, null, null);
		}
	}

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
	
	/**
	 * Sets the projection viewer for which we're reconciling.
	 * 
	 * @param viewer
	 */
	public void setProjectionViewer(final ProjectionViewer viewer) {
		projectionViewer = viewer;
		projectionViewer.setData(getClass().toString(), this);
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
					
					if (projectionViewer != null) {
						final ProjectionAnnotationModel model = projectionViewer.getProjectionAnnotationModel();
						final boolean block = foldBlockComments.get();
						final boolean pcal = foldPlusCalAlgorithm.get();
						final boolean translated = foldTranslatedPlusCalBlock.get();

						// We could do even more optimization than this, but this is better than none.
						if (block || pcal || translated) {
							for (final TLCProjectionAnnotation annotation : currentAnnotations) {
								final boolean collapse;

								switch (annotation.getTLCType()) {
									case BLOCK_COMMENT:
										collapse = block;
										break;
									case PCAL_BLOCK:
										collapse = pcal;
										break;
									default:
										collapse = translated;
								}

								if (collapse) {
									model.collapse(annotation);
								}
							}
						}
					}
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

		final FindReplaceDocumentAdapter search = new FindReplaceDocumentAdapter(document);
		
		// PCal location
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
					
					find = search.find(pcalStartLocation, "^\\s?\\*+\\)$", true, true, false, true);
					addProjectionAdditionToMap(additions, startLocation, find, AnnotationType.PCAL_BLOCK);
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
					addProjectionAdditionToMap(additions, translationStartLocation, find,
							AnnotationType.TRANSLATED_PCAL_BLOCK);
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
					addProjectionAdditionToMap(additions, lastFoundIndex, find, AnnotationType.BLOCK_COMMENT);
				}
				
				inBlock = !inBlock;
				lastFoundIndex = find.getOffset();
				find = search.find((lastFoundIndex + find.getLength()), BLOCK_COMMENT_DELIMITER_REGEX, true, true, false, true);
			}
		} catch (final BadLocationException ble) { }
		
		// 2 or more consecutive single line comments
		try {
			int lastFoundIndex = 0; // TODO future optimizations based on DocumentEvents' locations
			IRegion find = search.find(lastFoundIndex, SINGLE_LINE_COMMENT, true, true, false, true);
			
			int contiguousLineCount = 1;
			int firstMatchingOffset = -1;
			while (find != null) {
				if (firstMatchingOffset == -1) {
					firstMatchingOffset = find.getOffset();
				}
				lastFoundIndex = find.getOffset();
				final IRegion lineEnding = search.find((lastFoundIndex + find.getLength()), "\\n", true, true, false, true);
				if (lineEnding != null) {
					lastFoundIndex = lineEnding.getOffset();
					find = search.find((lastFoundIndex + 1), SINGLE_LINE_COMMENT, true, true, false, true);
				} else {
					// In this case the document has ended without a newline (but with a comment)
					lastFoundIndex += find.getLength();
					find = null;
				}
				
				boolean addProjection = (contiguousLineCount > 1);
				boolean reset = true;
				if ((find != null) && (find.getOffset() == (lastFoundIndex + 1))) {
					contiguousLineCount++;
					addProjection = false;
					reset = false;
				}
				if (addProjection) {
					addProjectionAdditionToMap(additions, firstMatchingOffset, lastFoundIndex,
											   AnnotationType.MULTIPLE_SINGLE_LINE_COMMENT);
				}
				if (reset) {
					contiguousLineCount = 1;
					firstMatchingOffset = -1;
				}
			}
		} catch (final BadLocationException ble) { }
		
		return additions;
    }

	private void addProjectionAdditionToMap(final Map<TLCProjectionAnnotation, Position> additions, final int startLocation,
										    final IRegion find, final AnnotationType type)
			throws BadLocationException {
		if (find != null) {
			final int endLocation = find.getOffset() + find.getLength() + 1;
			addProjectionAdditionToMap(additions, startLocation, endLocation, type);
		}
	}

	private void addProjectionAdditionToMap(final Map<TLCProjectionAnnotation, Position> additions, final int startLocation,
										    final int endLocation, final AnnotationType type)
			throws BadLocationException {
		final int length = endLocation - startLocation;
		final int positionLength = length + ((document.getLength() > endLocation) ? 1 : 0);	// +1 to cover the newline
		final Position position = new Position(startLocation, positionLength);

		additions.put(new TLCProjectionAnnotation(document.get(startLocation, length), type), position);
	}
	
	
	private enum AnnotationType {
		BLOCK_COMMENT,
		MULTIPLE_SINGLE_LINE_COMMENT,
		PCAL_BLOCK,
		TRANSLATED_PCAL_BLOCK;
	}
	
	// Nothing in the ProjectionAnnotation hierarchy implements equals/hashCode, we'd like such things to exist
	//		for reconciliation; also we denote classifications of annotations for folding groups.
	private static class TLCProjectionAnnotation extends ProjectionAnnotation {
		private final AnnotationType type;
		
		TLCProjectionAnnotation(final String text, final AnnotationType annotationType) {
			setText(text);
			
			type = annotationType;
		}
		
		AnnotationType getTLCType() {
			return type;
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
