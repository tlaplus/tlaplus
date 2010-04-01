package org.lamport.tla.toolbox.editor.basic.util;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.rules.IWhitespaceDetector;
import org.eclipse.jface.text.rules.IWordDetector;
import org.lamport.tla.toolbox.editor.basic.tla.TLAWhitespaceDetector;
import org.lamport.tla.toolbox.editor.basic.tla.TLAWordDetector;

import tla2sany.st.Location;

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

        return new Region(documentOffset - charCounter, charCounter + 1);
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

    /**
     * Converts four-int-location that is 1-based to a two int {@link IRegion} that is
     * 0-based.
     * 
     * TODO: unit test!
     * @param document
     * @param location
     * @return
     * @throws BadLocationException 
     */
    public static IRegion locationToRegion(IDocument document, Location location) throws BadLocationException
    {
        /* 
         * The coordinates returned by location are 1-based and the coordinates
         * for a region in a document should be 0-based to be consistent with Positions
         * in documents. Therefore, we subtract 1 from each location coordinate.
         */
        int offset = document.getLineOffset(location.beginLine() - 1) + location.beginColumn() - 1;
        /*
         * If location describes a two-character sequence beginning at column x, then it would
         * have location.endColumn() = x+1. This means that when computing the length, we add 1 to
         * the offset of the second point described by location. In other words, the offset of the
         * second point described by location is:
         * 
         * document.getLineOffset(location.endLine() - 1) + location.endColumn()-1
         * 
         * So the length is:
         * 
         * (document.getLineOffset(location.endLine() - 1) + location.endColumn()-1)+1 - offset
         * 
         * which equals:
         * 
         * document.getLineOffset(location.endLine() - 1) + location.endColumn() - offset
         */
        int length = document.getLineOffset(location.endLine() - 1) + location.endColumn() - offset;
        return new Region(offset, length);
    }

    /**
     * Returns a new region that ends at the end of the input region and begins
     * at the first character of the line before the line containing the offset
     * of the input region. If the input region's offset is on the first
     * line of the document, this method does nothing.
     * 
     * @param document
     * @param region
     * @return
     * @throws BadLocationException
     */
    public static IRegion getRegionWithPreviousLine(IDocument document, IRegion region) throws BadLocationException
    {
        // the first line of the region
        int currentFirstLine = document.getLineOfOffset(region.getOffset());
        if (currentFirstLine > 0)
        {
            int newOffset = document.getLineOffset(currentFirstLine - 1);
            return new Region(newOffset, region.getLength() + (region.getOffset() - newOffset));
        } else
        {
            // no previous line so do nothing
            return region;
        }

    }

}
