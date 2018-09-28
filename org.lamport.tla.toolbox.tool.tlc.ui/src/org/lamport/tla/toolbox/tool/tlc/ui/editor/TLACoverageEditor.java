package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.IAnnotationModelFactory;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.source.AnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationPresentation;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.texteditor.MarkerAnnotation;
import org.eclipse.ui.texteditor.ResourceMarkerAnnotationModel;
import org.eclipse.ui.texteditor.SourceViewerDecorationSupport;
import org.lamport.tla.toolbox.editor.basic.TLAEditorReadOnly;

public class TLACoverageEditor extends TLAEditorReadOnly {
	
	public static final String ANNOTATION_UNUSED = "toolbox.markers.tlc.coverage.unused";
	
	/* AnnotationPreference */
	
	private static final String ANNOTATION_USED_PREFIX = "toolbox.markers.tlc.coverage.covered.";

	public static class AnnotationPreference extends org.eclipse.ui.texteditor.AnnotationPreference {

		public AnnotationPreference(final long count, final long maxCount) {
			super(ANNOTATION_USED_PREFIX + Long.toString(count), ANNOTATION_USED_PREFIX + Long.toString(count) + ".colorKey", "",
					"", IAnnotationPresentation.DEFAULT_LAYER);
			this.setIncludeOnPreferencePage(false);
			this.setColorPreferenceValue(getRGB(count, maxCount));
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
		private static final float BLUE = 240;

		private RGB getRGB(final float val, final float maxval) {
			final float h = BLUE - ((val / maxval) * BLUE);
			// https://en.wikipedia.org/wiki/HSL_and_HSV
			return COLORS.computeIfAbsent(Math.round(h), hue -> new RGB(hue, .25f, 1f));
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
				final MarkerAnnotation createMarkerAnnotation = super.createMarkerAnnotation(marker);
				try {
					// For our programmatically created AnnotationPreferences above, the marker
					// annotation type has to be set manually.
					if (marker.getType().startsWith(ANNOTATION_USED_PREFIX)) {
						createMarkerAnnotation.setType(marker.getType());
					}
				} catch (final CoreException e) {
				}
				return createMarkerAnnotation;
			}
		}
	}

	/* TLACoverageEditor */
	
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

	@Override
	protected void configureSourceViewerDecorationSupport(SourceViewerDecorationSupport support) {
		prefs.values().forEach(p -> support.setAnnotationPreference(p));
		super.configureSourceViewerDecorationSupport(support);
	}
}
