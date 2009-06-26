package org.lamport.tla.toolbox.editor.basic.tla;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.SWT;
import org.lamport.tla.toolbox.editor.basic.TLAColorProvider;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;

/**
 * Syntactic code scanning and coloring
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLACodeScanner extends RuleBasedScanner
{
    /**
     * String quotes
     */
    public static final String STRING_QUOTES = "\"";
    /**
     * Single line comment
     */
    public static final String COMMENT_START_SEQUENCE = "\\*";

    /**
     * Construct the rules
     */
    public TLACodeScanner()
    {
        TLAColorProvider provider = TLAEditorActivator.getDefault().getTLAColorProvider();

        IToken keyword = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_KEYWORD), null, SWT.BOLD));
        IToken comment = new Token(new TextAttribute(provider.getColor(TLAColorProvider.COMMENT)));
        IToken value = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_VALUE)));
        IToken other = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_DEFAULT)));

        List rules = new ArrayList();

        // Add rule for single line comments.
        rules.add(new EndOfLineRule(COMMENT_START_SEQUENCE, comment)); //$NON-NLS-1$

        // Add rule for strings.
        rules.add(new SingleLineRule(STRING_QUOTES, STRING_QUOTES, value, '\\')); //$NON-NLS-2$ //$NON-NLS-1$

        // Add generic whitespace rule.
        rules.add(new WhitespaceRule(DocumentHelper.getDefaultWhitespaceDetector()));

        // Add word rule for standard words
        WordRule wordRule = new WordRule(DocumentHelper.getDefaultWordDetector(), other);
        
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
}
