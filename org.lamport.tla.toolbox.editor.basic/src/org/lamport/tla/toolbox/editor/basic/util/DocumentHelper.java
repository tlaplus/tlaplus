package org.lamport.tla.toolbox.editor.basic.util;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.rules.IWhitespaceDetector;
import org.eclipse.jface.text.rules.IWordDetector;
import org.lamport.tla.toolbox.editor.basic.tla.TLAWhitespaceDetector;
import org.lamport.tla.toolbox.editor.basic.tla.TLAWordDetector;

/**
 * Toolkit for document helper methods
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DocumentHelper
{

    /**
     * Factory method for the word detector
     */
    public static IWordDetector getDefaultWordDetector()
    {
        return new TLAWordDetector();
    }

    /**
     * Factory method for the whitespace detector
     */
    public static IWhitespaceDetector getDefaultWhitespaceDetector()
    {
        return new TLAWhitespaceDetector();
    }

    /**
     * At a given position in text retrieves the region marking the word, starting before and ending on current position 
     * @param document document
     * @param documentOffset offset (position of the cursor)
     * @param detector for identification of words 
     * @return a region expanded backwards
     */
    public static IRegion getRegionExpandedBackwards(IDocument document, int documentOffset, IWordDetector detector)
    {

        // Use string buffer to collect characters
        int charCounter = 0;
        while (true)
        {
            try
            {

                // Read character backwards
                char c = document.getChar(--documentOffset);

                // This was the start of a word
                if (!detector.isWordPart(c))
                    break;

                // Count character
                charCounter++;

            } catch (BadLocationException e)
            {

                // Document start reached, no word
                break;
            }
        }
        return new Region(documentOffset + 1, charCounter);
    }

    /**
     * At a given position in text retrieves the region marking the word, starting at and ending after the current position 
     * @param document document
     * @param documentOffset offset (position of the cursor)
     * @param detector for identification of words 
     * @return a region expanded forward
     */
    public static IRegion getRegionExpandedForwards(IDocument document, int documentOffset, IWordDetector detector)
    {

        // Use string buffer to collect characters
        int charCounter = 0;
        while (true)
        {
            try
            {
                // Read character forward
                char c = document.getChar(++documentOffset);

                // This was the start of a word
                if (!detector.isWordPart(c))
                    break;

                // Count character
                charCounter++;

            } catch (BadLocationException e)
            {

                // Document end reached, no word
                break;
            }
        }
        
        return new Region(documentOffset - charCounter, charCounter + 1 );
    }

    /**
     * Combines the effect of backwards and forwards region expansion
     * @param document
     * @param offset
     * @param defaultWordDetector
     * @return
     */
    public static IRegion getRegionExpandedBoth(IDocument document, int documentOffset, IWordDetector detector)
    {
        IRegion backwards = getRegionExpandedBackwards(document, documentOffset, detector);
        IRegion forwards = getRegionExpandedForwards(document, documentOffset, detector);
        return new Region(backwards.getOffset(), backwards.getLength() + forwards.getLength());
    }

}
