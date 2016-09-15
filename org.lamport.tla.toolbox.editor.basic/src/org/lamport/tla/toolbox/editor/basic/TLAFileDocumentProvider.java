package org.lamport.tla.toolbox.editor.basic;

import java.io.StringReader;
import java.io.StringWriter;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.texteditor.IDocumentProvider;

import tla2unicode.TLAUnicode;

public class TLAFileDocumentProvider extends TextFileDocumentProvider {
	public TLAFileDocumentProvider()  {
		super();
	}

	public void setDirty(Object element, boolean dirty) {
		FileInfo info= getFileInfo(element);
		if (info != null)
			info.fTextFileBuffer.setDirty(dirty);
	}
	
//	private static void a2u(IDocument doc) {
//		if (doc == null)
//			return;
//		final StringWriter out = new StringWriter();
//    	TLAUnicode.convert(true, new StringReader(doc.get()), out);
//    	doc.set(out.toString());
//	}
//	
//	private static void u2a(IDocument doc) {
//		if (doc == null)
//			return;
//    	final StringWriter out = new StringWriter();
//    	TLAUnicode.convert(false, new StringReader(doc.get()), out);
//    	doc.set(out.toString());
//	}
//	
//	public TLAFileDocumentProvider(IDocumentProvider parentProvider) {
//		super(parentProvider);
//	}
//	
//	@Override
//	protected FileInfo createFileInfo(Object element) throws CoreException {
//		return super.createFileInfo(element);
//	}
//	
//	@Override
//	public void connect(Object element) throws CoreException {
//		super.connect(element);
//		final IDocument document = getDocument(element);
//		a2u(document);
//	}
//	
//	@Override
//	public void synchronize(Object element) throws CoreException {
//		super.synchronize(element);
//		final IDocument document = getDocument(element);
//		a2u(document);
//	}
//	
//	@Override
//	protected void commitFileBuffer(IProgressMonitor monitor, FileInfo info, boolean overwrite) throws CoreException {
//		final IDocument document = info.fTextFileBuffer.getDocument();
//		try {
//			u2a(document);
//			super.commitFileBuffer(monitor, info, overwrite);
//		} finally {
////			a2u(document);
//	    }
//	}
//	
//	@Override
//	protected void createFileFromDocument(IProgressMonitor monitor, IFile file, IDocument document) throws CoreException {
//		try {
//			u2a(document);
//			super.createFileFromDocument(monitor, file, document);
//		} finally {
////			a2u(document);
//	    }
//	}
}
