package de.techjava.tla.ui.editors.scanner;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;

import de.techjava.tla.ui.editors.detector.TLACapitalizedWordDetector;
import de.techjava.tla.ui.editors.detector.TLACharDetector;
import de.techjava.tla.ui.editors.detector.TLAWhitespaceDetector;
import de.techjava.tla.ui.editors.rule.TLAIdentifierRule;
import de.techjava.tla.ui.editors.util.ITLAOperators;
import de.techjava.tla.ui.editors.util.ITLAReserveredWords;
import de.techjava.tla.ui.util.ColorManager;
import de.techjava.tla.ui.util.IColorManagerListener;
import de.techjava.tla.ui.util.ITLAEditorColorConstants;

/**
 * TLA+ reserved words scanner
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLASourceScanner.java,v 1.1 2005/08/22 15:43:37 szambrovski Exp $
 */
public class TLASourceScanner 
	extends RuleBasedScanner
	implements IColorManagerListener
{
    private Color	reservedColor;
    private Color	operationColor;
    private Color	identifierColor;
    private Color	textColor;
    
    private IToken 	reservedWordToken;
    private IToken 	operatorToken;
    private IToken 	identifierToken;
    private IToken 	other;
    
    private ColorManager manager;
    
    
    public TLASourceScanner(ColorManager manager)
    {
        this.manager = manager;
        this.manager.addColorManagerListener(this);
        
        this.colorManagerChanged();
        
		
		List rules = new ArrayList();


		// Add generic whitespace rule.
		rules.add(new WhitespaceRule(new TLAWhitespaceDetector()));

		// Add identifier rule
		rules.add(new TLAIdentifierRule(identifierToken));
		
		
		/* Add word rule for operators */
		WordRule operatorWordRule = new WordRule(new TLACharDetector(), other);
		for (int i= 0; i < ITLAOperators.ALL_OPERATOR_ARRAY.length; i++)
		{
			operatorWordRule.addWord(ITLAOperators.ALL_OPERATOR_ARRAY[i], operatorToken);
		}
		rules.add(operatorWordRule);
		
		/* Add word rule for reserved words */
		WordRule reservedWordRule = new WordRule(new TLACapitalizedWordDetector(), other);
		for (int i= 0; i < ITLAReserveredWords.ALL_WORDS_ARRAY.length; i++)
		{
		    reservedWordRule.addWord(ITLAReserveredWords.ALL_WORDS_ARRAY[i], reservedWordToken);
		}
		rules.add(reservedWordRule);

		IRule[] result= new IRule[rules.size()];
		rules.toArray(result);
		setRules(result);
    }


    /**
     * @see de.techjava.tla.ui.util.IColorManagerListener#colorManagerChanged()
     */
    public void colorManagerChanged() 
    {
        this.reservedColor 		= manager.getColor(ITLAEditorColorConstants.RESERVED);
        this.identifierColor 	= manager.getColor(ITLAEditorColorConstants.IDENTIFIER);
        this.operationColor 	= manager.getColor(ITLAEditorColorConstants.OPERATOR);
        this.textColor 			= manager.getColor(ITLAEditorColorConstants.TEXT);
		this.reservedWordToken 	= new Token( new TextAttribute(reservedColor, null, SWT.BOLD ));
		this.operatorToken 		= new Token( new TextAttribute(operationColor, null, SWT.BOLD));
		this.identifierToken 	= new Token( new TextAttribute(identifierColor, null, SWT.ITALIC));
		this.other				= new Token( new TextAttribute(textColor));

    }
}

/*
 * $Log: TLASourceScanner.java,v $
 * Revision 1.1  2005/08/22 15:43:37  szambrovski
 * sf cvs init
 *
 * Revision 1.4  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.3  2004/10/13 21:46:46  sza
 * bold operators
 *
 * Revision 1.2  2004/10/13 19:28:36  sza
 * refactrored
 *
 * Revision 1.1  2004/10/13 14:45:00  sza
 * operators added
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
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