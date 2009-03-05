package de.techjava.tla.ui.editors.annotation;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;

/**
 * Provide annotation information
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAAnnotationHover.java,v 1.1 2005/08/22 15:43:36 szambrovski Exp $
 */
public class TLAAnnotationHover 
	implements IAnnotationHover 
{

    /**
     * @see org.eclipse.jface.text.source.IAnnotationHover#getHoverInfo(org.eclipse.jface.text.source.ISourceViewer, int)
     */
    public String getHoverInfo(ISourceViewer sourceViewer, int lineNumber) 
    {
		IDocument document= sourceViewer.getDocument();

		try {
			IRegion info= document.getLineInformation(lineNumber);
			return document.get(info.getOffset(), info.getLength());
		} catch (BadLocationException x) {
		}

		return null;

    }

}

/*
 * $Log: TLAAnnotationHover.java,v $
 * Revision 1.1  2005/08/22 15:43:36  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/13 23:12:17  sza
 * hovers
 *
 *
 */