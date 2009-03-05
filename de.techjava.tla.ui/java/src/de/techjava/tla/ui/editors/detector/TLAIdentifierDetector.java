package de.techjava.tla.ui.editors.detector;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * Detects identifiers
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAIdentifierDetector.java,v 1.2 2005/09/29 11:31:44 sz9 Exp $
 */
public class TLAIdentifierDetector 
	implements IWordDetector 
{

    /**
     * @see org.eclipse.jface.text.rules.IWordDetector#isWordStart(char)
     */
    public boolean isWordStart(char c) 
    {
        // identifier always starts with a letter or an underscore
        return (Character.isLetter(c) || c == '_');
    }

    /**
     * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
     */
    public boolean isWordPart(char c) 
    {
        // identifier can be a letter, digit or underscore
        return (c == '_' || Character.isLetterOrDigit(c));
    }

}

/*
 * $Log: TLAIdentifierDetector.java,v $
 * Revision 1.2  2005/09/29 11:31:44  sz9
 * Fixed a few issues that led to identifiers not being recognized. More still open, in particular with identifiers that are preceded by a (, a !, or a <
 *
 * Revision 1.1  2005/08/22 15:43:37  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/20 22:42:31  sza
 * editor improvements
 *
 *
 */