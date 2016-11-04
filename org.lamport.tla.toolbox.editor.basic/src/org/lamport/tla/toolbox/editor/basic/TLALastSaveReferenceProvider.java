package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.AbstractDocument;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.internal.editors.quickdiff.LastSaveReferenceProvider;
import org.eclipse.ui.texteditor.ITextEditor;

import tla2unicode.TLAUnicode;

public class TLALastSaveReferenceProvider extends LastSaveReferenceProvider {
//	private TLAEditor fEditor;
    private long fModificationStamp = -1;
    
	@Override
	public IDocument getReference(IProgressMonitor monitor) {
		IDocument doc = super.getReference(monitor);
		if (TLAUnicodeReplacer.isUnicode()) {
			if (doc instanceof AbstractDocument) {
				final long mod = ((AbstractDocument)doc).getModificationStamp();
				if (mod != fModificationStamp) {
					// doc.set(fEditor.getAsciiDocument().get());
//					doc.set(TLAUnicode.convert(true, doc.get()));
					doc = new Document(TLAUnicode.convert(true, doc.get()));
					this.fModificationStamp = ((AbstractDocument) doc).getModificationStamp();
				}
			}
		}
		return doc;
	}

//	@Override
//	public void setActiveEditor(ITextEditor targetEditor) {
//		super.setActiveEditor(targetEditor);
//		if (targetEditor instanceof TLAEditor)
//			this.fEditor = (TLAEditor) targetEditor;
//	}
}
