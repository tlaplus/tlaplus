package de.techjava.tla.ui.editors.detector;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * Detects TLA+ words
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLACapitalizedWordDetector.java,v 1.1 2005/08/22 15:43:37 szambrovski Exp $
 */
public class TLACapitalizedWordDetector 
	implements IWordDetector
{

    public TLACapitalizedWordDetector()
    {
    }
    /**
     * @see org.eclipse.jface.text.rules.IWordDetector#isWordStart(char)
     */
    public boolean isWordStart(char c) 
    {
        return (Character.isUpperCase(c) ); 
    }

    /**
     * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
     */
    public boolean isWordPart(char c) 
    {
        return (Character.isUpperCase(c) );
    }

}

/*
 * $Log: TLACapitalizedWordDetector.java,v $
 * Revision 1.1  2005/08/22 15:43:37  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:11  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */