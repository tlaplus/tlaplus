package de.techjava.tla.ui.editors.rule;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWhitespaceDetector;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.Token;

import de.techjava.tla.ui.editors.detector.TLACharDetector;
import de.techjava.tla.ui.editors.detector.TLAWhitespaceDetector;
import de.techjava.tla.ui.editors.util.ITLAOperators;

/**
 * Encapsulates TLA + operator rule
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAOperatorRule.java,v 1.1 2005/08/22 15:43:32 szambrovski Exp $
 * @deprecated to be removed
 */
public class TLAOperatorRule 
	implements IRule 
{
    	private IWordDetector 		charWords;
    	private IWhitespaceDetector whitespace;
        private IToken 				token;
    	
    	public TLAOperatorRule(IToken token) 
    	{
    		charWords 	= new TLACharDetector();
    		whitespace	= new TLAWhitespaceDetector();
    		this.token 	= token;
    	}
    	/**
    	 * @see org.eclipse.jface.text.rules.IRule#evaluate(org.eclipse.jface.text.rules.ICharacterScanner)
    	 */
    	public IToken evaluate(ICharacterScanner scanner) 
    	{
			char start = (char) scanner.read();
			if (charWords.isWordStart(start)) 
			{
				String word = "" + start;
				char currentChar;
				while (charWords.isWordPart(currentChar = (char) scanner.read())) 
				{
					word += currentChar;
				}
				scanner.unread();
				if (whitespace.isWhitespace((char)scanner.read())) 
				{
				    scanner.unread();
					if (!ITLAOperators.ALL_OPERATOR_SET.contains(word)) 
					{
						return Token.UNDEFINED;
					} else {
					    return token;
					}
				} else {
					scanner.unread();
					return Token.UNDEFINED;
				}
			} else {
				scanner.unread();
				return Token.UNDEFINED;
			}
    	}
}

/*
 * $Log: TLAOperatorRule.java,v $
 * Revision 1.1  2005/08/22 15:43:32  szambrovski
 * sf cvs init
 *
 * Revision 1.3  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.2  2004/10/13 19:29:46  sza
 * marked as depricated
 *
 * Revision 1.1  2004/10/13 14:45:00  sza
 * operators added
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
 * Revision 1.1  2004/10/06 00:59:05  sza
 * initial commit
 *
 *
 */