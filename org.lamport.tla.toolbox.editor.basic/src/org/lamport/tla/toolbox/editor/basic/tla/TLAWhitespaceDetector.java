package org.lamport.tla.toolbox.editor.basic.tla;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * Detects whitespaces in TLA+ code
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAWhitespaceDetector implements IWhitespaceDetector
{

    /* (non-Javadoc)
     * Method declared on IWhitespaceDetector
     */
    public boolean isWhitespace(char character)
    {
        return Character.isWhitespace(character);
    }
}