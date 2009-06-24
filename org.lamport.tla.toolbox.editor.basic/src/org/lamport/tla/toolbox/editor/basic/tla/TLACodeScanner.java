package org.lamport.tla.toolbox.editor.basic.tla;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWhitespaceDetector;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.SWT;
import org.lamport.tla.toolbox.editor.basic.TLAColorProvider;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;

/**
 * Syntactic code scanning and coloring
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLACodeScanner extends RuleBasedScanner
{

    public TLACodeScanner()
    {
        TLAColorProvider provider = TLAEditorActivator.getDefault().getTLAColorProvider();

        IToken keyword = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_KEYWORD), null, SWT.BOLD));
        IToken comment = new Token(new TextAttribute(provider.getColor(TLAColorProvider.COMMENT)));
        IToken value = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_VALUE)));
        IToken other = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_DEFAULT)));

        List rules = new ArrayList();

        // Add rule for single line comments.
        rules.add(new EndOfLineRule("\\*", comment)); //$NON-NLS-1$

        // Add rule for strings.
        rules.add(new SingleLineRule("\"", "\"", value, '\\')); //$NON-NLS-2$ //$NON-NLS-1$

        // Add generic whitespace rule.
        rules.add(new WhitespaceRule(new TLAWhitespaceDetector()));

        // Add word rule for standard words
        WordRule wordRule = new WordRule(new TLAWordDetector(), other);
        
        // add values
        for (int i = 0; i < ITLAReserveredWords.ALL_VALUES_ARRAY.length; i++)
        {
            wordRule.addWord(ITLAReserveredWords.ALL_VALUES_ARRAY[i], value);
        }
        
        // add reserved words
        for (int i = 0; i < ITLAReserveredWords.ALL_WORDS_ARRAY.length; i++)
        {
            wordRule.addWord(ITLAReserveredWords.ALL_WORDS_ARRAY[i], keyword);
        }
        
        rules.add(wordRule);

        IRule[] result = new IRule[rules.size()];
        rules.toArray(result);
        setRules(result);
    }

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
}
