package de.techjava.tla.ui.editors.annotation;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.swt.graphics.Point;

/**
 * Provides text hoover information
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLATextHover.java,v 1.1 2005/08/22 15:43:36 szambrovski Exp $
 */
public class TLATextHover 
	implements ITextHover
{

    /**
     * @see org.eclipse.jface.text.ITextHover#getHoverInfo(org.eclipse.jface.text.ITextViewer, org.eclipse.jface.text.IRegion)
     */
    public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) 
    {
		if (hoverRegion != null) {
			try {
				if (hoverRegion.getLength() > -1)
					return textViewer.getDocument().get(hoverRegion.getOffset(), hoverRegion.getLength());
			} catch (BadLocationException bse) 
			{
			}
		}
		return "Empty selection";
    }

    /**
     * @see org.eclipse.jface.text.ITextHover#getHoverRegion(org.eclipse.jface.text.ITextViewer, int)
     */
    public IRegion getHoverRegion(ITextViewer textViewer, int offset) 
    {
		Point selection = textViewer.getSelectedRange();
		if (selection.x <= offset && offset < selection.x + selection.y)
		{
			return new Region(selection.x, selection.y);
		}
		return new Region(offset, 0);
    }

}

/*
 * $Log: TLATextHover.java,v $
 * Revision 1.1  2005/08/22 15:43:36  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/13 23:12:17  sza
 * hovers
 *
 *
 */