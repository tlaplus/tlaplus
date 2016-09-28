package org.lamport.tla.toolbox.editor.basic;

import java.io.StringReader;
import java.io.StringWriter;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.IElementStateListener;
import org.eclipse.ui.texteditor.MarkerAnnotation;
import org.eclipse.ui.texteditor.MarkerUtilities;
import org.eclipse.ui.texteditor.ResourceMarkerAnnotationModel;
import org.lamport.tla.toolbox.editor.basic.util.ElementStateAdapter;

import tla2sany.st.Location;
import tla2unicode.TLAUnicode;
import util.UniqueString;

public class TLAFileDocumentProvider extends TextFileDocumentProvider {
	// Used to map Unicode token locations to their ASCII location
    
    
	public TLAFileDocumentProvider()  {
		super();
		init();
	}
	
	public TLAFileDocumentProvider(IDocumentProvider parentProvider) {
		super(parentProvider);
		init();
	}
	
	private void init() {
		addElementStateListener(new ElementStateAdapter() {
			
			@Override
			public void elementDirtyStateChanged(Object element, boolean isDirty) {
			}
			
			@Override
			public void elementContentReplaced(Object element) {
				setUnicode0(getFileInfo(element), TLAUnicodeReplacer.UNICODE_MODE);
			}
		});
	}
	
	@Override
	protected FileInfo createFileInfo(Object element) throws CoreException {
		FileInfo info = new FileInfo(super.createFileInfo(element));
		((TLAMarkerAnnotationModel)info.fModel).info = info;
		return info;
	}

	protected FileInfo getFileInfo(Object element)  {
		return (FileInfo) super.getFileInfo(element);
	}
	
	@Override
	protected IAnnotationModel createAnnotationModel(IFile file) {
		return new TLAMarkerAnnotationModel(file);
	}
	
	
	static protected class FileInfo extends TextFileDocumentProvider.FileInfo {
		private TLAUnicode.TokenPosition locationConverter;
	    private Document asciiDoc;
	    
		FileInfo(TextFileDocumentProvider.FileInfo other) {
			this.fElement = other.fElement;
			this.fCount = other.fCount;
			this.fTextFileBuffer = other.fTextFileBuffer;
			this.fTextFileBufferLocationKind = other.fTextFileBufferLocationKind;
			this.fModel = other.fModel;
			this.fCachedReadOnlyState = other.fCachedReadOnlyState;
		}
	}
	
	private IDocument getDocument(FileInfo info) {
		return info.fTextFileBuffer.getDocument();
	}
	
	private void setDirty(FileInfo info, boolean dirty) {
		if (info != null)
			info.fTextFileBuffer.setDirty(dirty);
	}
	
	public void setDirty(Object element, boolean dirty) {
		setDirty(getFileInfo(element), dirty);
	}
	
	public boolean isUnicode() {
    	return TLAUnicodeReplacer.UNICODE_MODE;
    }
	
	public IDocument getAsciiDocument(Object element) {
		FileInfo info = getFileInfo(element);
		return info != null ? info.asciiDoc : null;
	}
    
//    private class AnnotationModelListener implements IAnnotationModelListener, IAnnotationModelListenerExtension {
//    	private boolean recursive;
//    	
//		@Override
//		public void modelChanged(AnnotationModelEvent event) {
//			if (recursive)
//				return;
//			recursive = true;
//			try {
//				final AnnotationModel am = (AnnotationModel)event.getAnnotationModel(); 
//				for (Annotation ann : event.getAddedAnnotations())
//					am.modifyAnnotationPosition(ann, convertPosition(false, am.getPosition(ann)));
//			} finally {
//				recursive = false;
//			}
//		}
//
//		@Override
//		public void modelChanged(IAnnotationModel model) {
//			throw new AssertionError("Shouldn't be called");	
//		}
//    }
    
    private class TLAMarkerAnnotationModel extends ResourceMarkerAnnotationModel {
    	FileInfo info;
    	
		public TLAMarkerAnnotationModel(IResource resource) {
			super(resource);
		}

		@Override
		protected void addAnnotation(Annotation annotation, Position position, boolean fireModelChanged) throws BadLocationException {
			position = convertPosition(info, false, annotation, position);
			super.addAnnotation(annotation, position, fireModelChanged);
		}
		@Override
		public boolean updateMarker(IMarker marker, IDocument document, Position position) throws CoreException {
			position = convertPosition(info, false, position);
			return super.updateMarker(marker, document, position);
		}

		@Override
		public boolean updateMarker(IDocument document, IMarker marker, Position position) throws CoreException {
			position = convertPosition(info, false, marker, position);
			return super.updateMarker(document, marker, position);
		}
    }
    
	@Override
	public void connect(Object element) throws CoreException {
		super.connect(element);
		setUnicode0(getFileInfo(element), TLAUnicodeReplacer.UNICODE_MODE);
	}
	
	@Override
	public void synchronize(Object element) throws CoreException {
		super.synchronize(element);
		setUnicode0(getFileInfo(element), TLAUnicodeReplacer.UNICODE_MODE);
	}
	
	@Override
	protected void commitFileBuffer(IProgressMonitor monitor, TextFileDocumentProvider.FileInfo info, boolean overwrite) throws CoreException {
		final boolean unicode = TLAUnicodeReplacer.UNICODE_MODE;
		try {
			if (unicode) {
				setUnicode0((FileInfo) info, false);
				setDirty((FileInfo) info, true);
			}
			super.commitFileBuffer(monitor, info, overwrite);
		} finally {
			if (unicode)
				setUnicode0((FileInfo) info, true);
	    }
	}
	
	
	@Override
	protected void createFileFromDocument(IProgressMonitor monitor, IFile file, IDocument document) throws CoreException {
		final boolean unicode = TLAUnicodeReplacer.UNICODE_MODE;
		try {
			if (unicode)
				setUnicode0(document, false);
			super.createFileFromDocument(monitor, file, document);
		} finally {
			if (unicode)
				setUnicode0(document, true);
	    }
	}
    
	////////
    
	 // screen: is the given location in editor coordinates
    public Location convertLocation(Object element, boolean screen, Location location) {
    	return convertLocation(getFileInfo(element), screen, location);
    }
    
    public Location convertLocation(FileInfo info, boolean screen, Location location) {
    	if (location == null)
    		return null;
    	System.out.println("&&&from: " + location);
    	if (isUnicode())
    		location = new Location(location.source() != null ? UniqueString.uniqueStringOf(location.source()) : null, 
        		location.beginLine(), convertColumn(info, screen, location.beginLine() - 1, location.beginColumn()), 
        		location.endLine(), convertColumn(info, screen, location.endLine() - 1, location.endColumn()));
    	System.out.println("&&&to: " + location);
    	return location;
    }
    
    public Position convertPosition(Object element, boolean screen, Position position) {
    	return convertPosition(getFileInfo(element), screen, position);
    }
    
    private Position convertPosition(FileInfo info, boolean screen, Annotation annotation, Position position) {
    	if (annotation instanceof MarkerAnnotation)
    		return convertPosition(info, screen, ((MarkerAnnotation) annotation).getMarker(), position);
    	else
    		return convertPosition(info, screen, position);
    }
    
    private Position convertPosition(FileInfo info, boolean screen, IMarker marker, Position position) {
		if (MarkerUtilities.getCharStart(marker) == -1 && MarkerUtilities.getCharEnd(marker) == -1) {
			try {
				// marker line number is 1-based
				int line = MarkerUtilities.getLineNumber(marker) - 1;
				final IDocument doc = getDocument(info);
				final IDocument asciiDoc = info.asciiDoc;
				final IDocument toDoc = !screen ? doc : asciiDoc;
				return new Position(toDoc.getLineOffset(line), 0);
			} catch (BadLocationException e) {
				return null;
			}
		}
    	return convertPosition(info, screen, position);
    }
    
    public Position convertPosition(FileInfo info, boolean screen, Position position) {
    	if (position == null)
    		return null;
    	System.out.println("&&&from: " + position);
    	boolean deleted = position.isDeleted;
    	if (isUnicode()) {
    		int offset = convertOffset(info, screen, position.getOffset());
        	int end = convertOffset(info, screen, position.getOffset() + position.getLength());
        	int length = end - offset;
    		position = new Position(offset, length);
    		if (deleted)
    			position.delete();
    	}
    	System.out.println("&&&to: " + position);
    	return position;
    }
    
 // screen: is the given offset in editor coordinates
    public int convertOffset(Object element, boolean screen, int offset) {
    	return convertOffset(getFileInfo(element), screen, offset);
    }
    
    private int convertOffset(FileInfo info, boolean screen, int offset) {
		if (!isUnicode())
			return offset;
		if (info == null)
			return -1;
		final IDocument doc = getDocument(info);
		final TLAUnicode.TokenPosition locationConverter = info.locationConverter;
		final IDocument asciiDoc = info.asciiDoc;
		
		try {
			System.out.println("&&&from: " + offset);
			final IDocument fromDoc = screen ? doc : asciiDoc;
			final IDocument toDoc = !screen ? doc : asciiDoc;

			final int line = fromDoc.getLineOfOffset(offset);
			System.out.println("&&&fromLine: " + line);
			System.out.println("&&&toLine: " + toDoc.getLineOfOffset(offset));
			final int lineOffset = fromDoc.getLineOffset(line);
			final int column = offset - lineOffset;
			
			final int lineLength = toDoc.getLineLength(line);
			offset = toDoc.getLineOffset(line) + Math.min(locationConverter.convert(!screen, line, column), lineLength);
			System.out.println("&&&to: " + offset);
			return offset;
		} catch (BadLocationException e) {
			return -1;
		}
    }
    
    public IRegion convertRegion(Object element, boolean screen, IRegion region) {
    	int start = convertOffset(element, screen, region.getOffset());
    	int end = convertOffset(element, screen, region.getOffset() + region.getLength());
    	return new Region(start, end - start);
    }
    
    // screen: is the given location in editor coordinates
    private int convertColumn(FileInfo info, boolean screen, int line, int column) {
		if (!isUnicode())
			return column;
		if (info == null)
			return -1;
		final IDocument doc = getDocument(info);
		final TLAUnicode.TokenPosition locationConverter = info.locationConverter;
		try {
			int lineLength = doc.getLineLength(line);
			return Math.min(locationConverter.convert(!screen, line, column), lineLength);
		} catch (BadLocationException e) {
			return -1;
		}
    }
	
	private void setUnicode0(FileInfo info, boolean unicode) {
		if (info == null)
			return;
		final IDocument doc = getDocument(info);
		if (doc == null)
			return;
		
		final String orig = doc.get();
    	final TLAUnicode.TokenPosition locConverter = setUnicode0(doc, unicode);
    	
    	info.locationConverter = unicode ? locConverter : null;
    	info.asciiDoc = new Document(orig);
    	setDirty(info, false);
    	
//    	captureUndo(1);    	
	}
	
	private TLAUnicode.TokenPosition setUnicode0(IDocument doc, boolean unicode) {
		final String orig = doc.get();
		final StringWriter out = new StringWriter();
    	final TLAUnicode.TokenPosition locConverter = TLAUnicode.convert(unicode, new StringReader(orig), out);
    	doc.set(out.toString());
    	return locConverter;
	}
}
