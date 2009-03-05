package de.techjava.tla.ui.editors.rule;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.Token;

import de.techjava.tla.ui.editors.detector.TLACharDetector;
import de.techjava.tla.ui.editors.detector.TLAIdentifierDetector;
import de.techjava.tla.ui.editors.detector.TLAWhitespaceDetector;
import de.techjava.tla.ui.editors.util.ITLAReserveredWords;

/**
 * Evaluate identifiers
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAIdentifierRule.java,v 1.1 2005/08/22 15:43:32 szambrovski Exp $
 */
public class TLAIdentifierRule 
	implements IRule 
{
    private IWordDetector 			detector;
    private TLAWhitespaceDetector 	whitespace;
    private TLACharDetector 		chars;
    private IToken 					token;
    
    
    /**
     * @param detector
     */
    public TLAIdentifierRule(IToken token) 
    {
        this.detector 	= new TLAIdentifierDetector();
        this.whitespace	= new TLAWhitespaceDetector();
        this.chars		= new TLACharDetector();
        this.token 		= token;
    }

    /**
     * @see org.eclipse.jface.text.rules.IRule#evaluate(org.eclipse.jface.text.rules.ICharacterScanner)
     */
    public IToken evaluate(ICharacterScanner scanner) 
    {
		char start = (char) scanner.read(); 
		if (detector.isWordStart(start)) 
		{
			String word = "" + start;
			char currentChar;
			while (detector.isWordPart(currentChar = (char) scanner.read())) 
			{
				word += currentChar;
			}
			scanner.unread();
			char terminator = (char)scanner.read();
			if (	whitespace.isWhitespace(terminator) || chars.isWordStart(terminator) ) 
			{
			    
			    scanner.unread();	// unread terminator
			    
				if (	!ITLAReserveredWords.ALL_WORDS_SET.contains(word) 
				        && !word.startsWith("WF_")
				        && !word.startsWith("SF_")) 
				{
				    return token;
				} else {
				    for (int i = word.length() - 1 ; i >= 0; i--) 
				    {
				        scanner.unread();    
				    }
				    return Token.UNDEFINED;
				}
			} else {
				scanner.unread();	// unread terminator

				return Token.UNDEFINED;
			}
		} else {
			scanner.unread();	// unread start char
			return Token.UNDEFINED;
		}

    }

}

/*
 * $Log: TLAIdentifierRule.java,v $
 * Revision 1.1  2005/08/22 15:43:32  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/20 22:42:31  sza
 * editor improvements
 *
 *
 */