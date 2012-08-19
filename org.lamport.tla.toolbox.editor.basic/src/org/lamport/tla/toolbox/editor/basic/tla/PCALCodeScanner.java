package org.lamport.tla.toolbox.editor.basic.tla;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.SWT;
import org.lamport.tla.toolbox.editor.basic.TLAColorProvider;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;

/**
 * Syntactic code scanning and coloring
 * 
 * This is a clone of TLACodeScanner modified for PlusCal by LL.
 * The original was written by:
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PCALCodeScanner extends RuleBasedScanner
{
    /**
     * Construct the rules
     */
    public PCALCodeScanner()
    {
        TLAColorProvider provider = TLAEditorActivator.getDefault().getTLAColorProvider();

        IToken keyword = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_KEYWORD), null, SWT.BOLD));
        IToken value = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_VALUE)));
        IToken other = new Token(new TextAttribute(provider.getColor(TLAColorProvider.TLA_DEFAULT)));
        IToken pcal = new Token(new TextAttribute(provider.getColor(TLAColorProvider.PCAL_KEYWORD)));
        
        List rules = new ArrayList();

        // Add generic whitespace rule.
        // rules.add(new WhitespaceRule(DocumentHelper.getDefaultWhitespaceDetector()));

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
        
     // add PlusCal keywords
        for (int i = 0; i < ITLAReserveredWords.PCAL_WORDS_ARRAY.length; i++)
        {
            wordRule.addWord(ITLAReserveredWords.PCAL_WORDS_ARRAY[i], pcal);
        }
        
        rules.add(wordRule);

        IRule[] result = new IRule[rules.size()];
        rules.toArray(result);
        setRules(result);
    }
}
