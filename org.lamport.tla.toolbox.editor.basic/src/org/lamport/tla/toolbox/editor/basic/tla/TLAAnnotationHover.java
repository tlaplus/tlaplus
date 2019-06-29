package org.lamport.tla.toolbox.editor.basic.tla;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.eclipse.core.resources.IMarker;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.texteditor.MarkerAnnotation;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAAnnotationHover implements IAnnotationHover {
    /**
     * {@inheritDoc}
     */
	public String getHoverInfo(final ISourceViewer sourceViewer, final int lineNumber) {
		final String[] messages = getMessagesForLine(sourceViewer, lineNumber);

		if (messages.length == 0) {
			return null;
		}

		final StringBuilder sb = new StringBuilder();
		final String lineSeparator = System.getProperty("line.separator");
		for (int i = 0; i < messages.length; i++) {
			sb.append(messages[i]);
			if (i < (messages.length - 1)) {
				sb.append(lineSeparator);
			}
		}
		
		return sb.toString();
	}

	private String[] getMessagesForLine(final ISourceViewer viewer, final int line) {
		final IAnnotationModel model = viewer.getAnnotationModel();

		if (model == null) {
			return new String[0];
		}

		final Iterator<Annotation> it = model.getAnnotationIterator();
		final IDocument document = viewer.getDocument();
		final ArrayList<String> messages = new ArrayList<>();
		final HashMap<Position, Set<String>> placeMessagesMap = new HashMap<>();
		while (it.hasNext()) {
			final Annotation annotation = it.next();
			if (annotation instanceof MarkerAnnotation) {
				final MarkerAnnotation ma = (MarkerAnnotation) annotation;
				final Position p = model.getPosition(ma);
				if (compareRulerLine(p, document, line)) {
					final IMarker marker = ma.getMarker();
					final String message = marker.getAttribute(IMarker.MESSAGE, null);
					if ((message != null) && (message.trim().length() > 0)) {
						Set<String> priorMessages = placeMessagesMap.get(p);
						if (priorMessages == null) {
							priorMessages = new HashSet<>();
							placeMessagesMap.put(p, priorMessages);
						}
						
						if (!priorMessages.contains(message)) {
							messages.add(message);
							priorMessages.add(message);
						}
					}
				}
			}
		}
		return (String[]) messages.toArray(new String[messages.size()]);
	}

	private boolean compareRulerLine(final Position position, final IDocument document, final int line) {
		try {
			if ((position.getOffset() > -1) && (position.getLength() > -1)) {
				return (document.getLineOfOffset(position.getOffset()) == line);
			}
		} catch (final BadLocationException e) { }
		return false;
	}
}
