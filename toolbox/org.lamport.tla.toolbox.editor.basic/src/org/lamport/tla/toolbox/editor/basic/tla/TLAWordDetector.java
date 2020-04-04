package org.lamport.tla.toolbox.editor.basic.tla;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * Detects TLA+ words
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAWordDetector implements IWordDetector
{

    /* (non-Javadoc)
     * Method declared on IWordDetector.
     */
    public boolean isWordPart(char character)
    {
        return Character.isJavaIdentifierPart(character);
    }

    /* (non-Javadoc)
     * Method declared on IWordDetector.
     */
    public boolean isWordStart(char character)
    {
        return Character.isJavaIdentifierStart(character);
    }
}

