package org.lamport.tla.toolbox.util;

import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IOverviewRuler;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.widgets.Composite;
import org.lamport.tla.toolbox.editor.basic.TLAUnicodeReplacer;
import org.osgi.service.event.Event;
import org.osgi.service.event.EventHandler;

import tla2unicode.Unicode;

public class TLASourceViewer extends SourceViewer {
	private EventHandler eventHandler;
	private boolean converting;
	
	public TLASourceViewer(Composite parent, IVerticalRuler ruler, int styles) {
		super(parent, ruler, styles);
	}

	public TLASourceViewer(Composite parent, IVerticalRuler verticalRuler, IOverviewRuler overviewRuler,
			boolean showAnnotationsOverview, int styles) {
		super(parent, verticalRuler, overviewRuler, showAnnotationsOverview, styles);
	}

	private synchronized EventHandler getEventHandler() {
		if (eventHandler == null) {
			this.eventHandler = new EventHandler() {
				@Override
				public void handleEvent(Event event) {
					if (event == null)
						return;
					final Object value = event.getProperty(IEventBroker.DATA);
					switch (event.getTopic()) {
					case TLAUnicodeReplacer.EVENTID_TOGGLE_UNICODE:
						unicodeToggleHandler((Boolean)value);
						break;
					default:		
					}
				}
			};
		}
		return eventHandler;
	}
	
	@Override
	public void setDocument(IDocument document, IAnnotationModel annotationModel, int modelRangeOffset, int modelRangeLength) {
		convert(TLAUnicodeReplacer.isUnicode(), document);
		super.setDocument(document, annotationModel, modelRangeOffset, modelRangeLength);
	}

	@Override
	protected void createControl(Composite parent, int styles) {
		super.createControl(parent, styles);
		UIHelper.getEventBroker().subscribe(TLAUnicodeReplacer.EVENTID_TOGGLE_UNICODE, getEventHandler());
	}

	@Override
	protected void handleDispose() {
		UIHelper.getEventBroker().unsubscribe(eventHandler);
		super.handleDispose();
	}
	
	private void unicodeToggleHandler(boolean unicode) {
		convert(unicode, getDocument());
	}
	
	@Override
	protected void updateTextListeners(WidgetCommand cmd) {
		if (converting) // prevent the model from being marked dirty due to unicode toggle
			return; // if does not work, temporarily remove instances of DirtyMarkingListener from fTextListeners
		super.updateTextListeners(cmd);
	}

	private void convert(boolean unicode, IDocument doc) {
		if (doc == null)
			return;
		converting = true;
		try {
			doc.set(Unicode.convert(unicode, doc.get()));
		} finally {
			converting = false;
		}
	}
}
