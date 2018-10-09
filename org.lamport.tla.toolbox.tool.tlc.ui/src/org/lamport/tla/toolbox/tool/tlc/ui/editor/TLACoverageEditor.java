/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeSet;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.IAnnotationModelFactory;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.DefaultTextHover;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationModel;
import org.eclipse.jface.text.source.IAnnotationAccess;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationPresentation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.texteditor.DefaultMarkerAnnotationAccess;
import org.eclipse.ui.texteditor.MarkerAnnotation;
import org.eclipse.ui.texteditor.ResourceMarkerAnnotationModel;
import org.eclipse.ui.texteditor.SourceViewerDecorationSupport;
import org.lamport.tla.toolbox.editor.basic.TLAEditorReadOnly;
import org.lamport.tla.toolbox.editor.basic.TLASourceViewerConfiguration;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.TLACoverageEditor.Factory.MyMarkerAnnotation;

public class TLACoverageEditor extends TLAEditorReadOnly {
	
	public static final String ANNOTATION_UNUSED = "toolbox.markers.tlc.coverage.unused";
	
	/* AnnotationPreference */
	
	private static final String ANNOTATION_USED_PREFIX = "toolbox.markers.tlc.coverage.covered.";

	public static class AnnotationPreference extends org.eclipse.ui.texteditor.AnnotationPreference {

		public AnnotationPreference(final int count) {
			super(ANNOTATION_USED_PREFIX + Long.toString(count), ANNOTATION_USED_PREFIX + Long.toString(count) + ".colorKey", "",
					"", IAnnotationPresentation.DEFAULT_LAYER);
			this.setIncludeOnPreferencePage(false);
			this.setColorPreferenceValue(getRGB(count));
			// The Highlight* has to match the
			// org.eclipse.ui.editors.markerAnnotationSpecification defined in the
			// plugin.xml even though markerAnnotationSpecification isn't used. However, it
			// seems this triggers some internal initialization of the Annotation handling
			// without which highlighting does not work.
			// The basic crux is that the Annotation handling is completely over-engineered
			// but does not allow to dynamically adapt an Annotation depending on the
			// attributed of an IMarker.
			this.setHighlightPreferenceKey(ANNOTATION_USED_PREFIX + "prototype");
			this.setHighlightPreferenceValue(true);
		}

		// Cache RGB instances because they are expensive.
		private static final Map<Integer, RGB> COLORS = new HashMap<>();

		private RGB getRGB(final int val) {
			return COLORS.computeIfAbsent(val, hue -> new RGB(hue, .25f, 1f));
		}
	}
	
	/* IAnnotationModelFactory */

	public static class Factory implements IAnnotationModelFactory {
		@Override
		public IAnnotationModel createAnnotationModel(final IPath location) {
			// Copied from org.eclipse.ui.texteditor.ResourceMarkerAnnotationModelFactory
			final IFile file= FileBuffers.getWorkspaceFileAtLocation(location);
			if (file != null) {
				return new MyResourceMarkerAnnotationModel(file);
			}
			return new AnnotationModel();
		}
		
		public class MyResourceMarkerAnnotationModel extends ResourceMarkerAnnotationModel {

			public MyResourceMarkerAnnotationModel(final IFile file) {
				super(file);
			}

			@Override
			protected MarkerAnnotation createMarkerAnnotation(final IMarker marker) {
				try {
					// For our programmatically created AnnotationPreferences above, the marker
					// annotation type has to be set manually.
					if (marker.getType().startsWith(ANNOTATION_USED_PREFIX)) {
						return new MyMarkerAnnotation(marker);
					}
				} catch (final CoreException e) {
				}
				return super.createMarkerAnnotation(marker);
			}
		}
		
		public static class MyMarkerAnnotation extends MarkerAnnotation {

			public MyMarkerAnnotation(final IMarker marker) throws CoreException {
				super(marker);
				this.setType(marker.getType());
			}

			@Override
			public int getLayer() {
				return getMarker().getAttribute(LAYER, 0);
			}
		}
	}

	/* TLACoverageEditor */

	public static final String LAYER = "tlacoverageeditor.layer";

	private final Map<Long, org.eclipse.ui.texteditor.AnnotationPreference> prefs;

	public TLACoverageEditor(Map<Long, org.eclipse.ui.texteditor.AnnotationPreference> map) {
		this.prefs = map;
		
		final IPreferenceStore preferenceStore = getPreferenceStore();
		for (final org.eclipse.ui.texteditor.AnnotationPreference ap : prefs.values()) {
			final RGB colorPreferenceValue = ap.getColorPreferenceValue();
			final String format = String.format("%s,%s,%s", colorPreferenceValue.red, colorPreferenceValue.green,
					colorPreferenceValue.blue);
			preferenceStore.setValue(ap.getColorPreferenceKey(), format);
		}
	}
	
	// Show the actual coverage count/value in a mouse-over hover.
    protected TLASourceViewerConfiguration getTLASourceViewerConfiguration(IPreferenceStore preferenceStore) {
    	return new TLACoverageSourceViewerConfiguration(preferenceStore, this); 
    }

    private static class TLACoverageSourceViewerConfiguration extends TLASourceViewerConfiguration {

		public TLACoverageSourceViewerConfiguration(IPreferenceStore preferenceStore,
				TLACoverageEditor tlaCoverageEditor) {
			super(preferenceStore, tlaCoverageEditor);
		}

		@Override
		public ITextHover getTextHover(final ISourceViewer sourceViewer, String contentType) {
			return new DefaultTextHover(sourceViewer) {
				
				@Override
				public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
					final IAnnotationModel model = sourceViewer.getAnnotationModel();

					// Compared to DefaultTextHover, this implementation takes the annotation's layer into account.
					final TreeSet<Annotation> layers = new TreeSet<Annotation>(new Comparator<Annotation>() {
						@Override
						public int compare(Annotation a1, Annotation a2) {
							if (a1 instanceof MyMarkerAnnotation & a2 instanceof MyMarkerAnnotation) {
								final MyMarkerAnnotation m1 = (MyMarkerAnnotation) a1;
								final MyMarkerAnnotation m2 = (MyMarkerAnnotation) a2;
								return Integer.compare(m1.getLayer(), m2.getLayer());
							}
							return 0;
						}
					});
					final Iterator<Annotation> e= model.getAnnotationIterator();
					while (e.hasNext()) {
						final Annotation a= e.next();
						if (isIncluded(a)) {
							final Position p= model.getPosition(a);
							if (p != null && p.overlapsWith(hoverRegion.getOffset(), hoverRegion.getLength())) {
								final String msg= a.getText();
								if (msg != null && msg.trim().length() > 0) {
									layers.add(a);
								}
							}
						}
					}
					if (layers.isEmpty()) {
						return null;
					}
					return layers.last().getText();
				}
			};
		}
    }
    

	@Override
	protected void configureSourceViewerDecorationSupport(SourceViewerDecorationSupport support) {
		prefs.values().forEach(p -> support.setAnnotationPreference(p));
		super.configureSourceViewerDecorationSupport(support);
	}
	
	@Override
	protected IAnnotationAccess createAnnotationAccess() {
		return new MyDefaultMarkerAnnotationAccess();
	}
	
	public static class MyDefaultMarkerAnnotationAccess extends DefaultMarkerAnnotationAccess {

		@SuppressWarnings("deprecation")
		@Override
		public int getLayer(final Annotation annotation) {
			if (annotation instanceof MarkerAnnotation) {
				final MarkerAnnotation ma = (MarkerAnnotation) annotation;
				return ma.getLayer();
			}
			return super.getLayer(annotation);
		}
	}
}
