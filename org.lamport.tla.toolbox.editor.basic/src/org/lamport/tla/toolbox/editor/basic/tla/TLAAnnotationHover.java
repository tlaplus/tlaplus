package org.lamport.tla.toolbox.editor.basic.tla;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAAnnotationHover implements IAnnotationHover
{

    /* (non-Javadoc)
     * Method declared on IAnnotationHover
     */
    public String getHoverInfo(ISourceViewer sourceViewer, int lineNumber)
    {
        IDocument document = sourceViewer.getDocument();

        /*
        try
        {
            IRegion info = document.getLineInformation(lineNumber);
            return "This is an annotation for: " + document.get(info.getOffset(), info.getLength());
        } catch (BadLocationException x)
        {
        }
*/
        return null;
    }
}
