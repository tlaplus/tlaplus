package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.SWT;

/**
 * Syntactic code scanning and coloring
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLACodeScanner extends RuleBasedScanner
{
    public static String[] KEYWORDS = { "CONSTANT", "VARIABLE" };

    public TLACodeScanner()
    {
        TLAColorProvider provider = TLAEditorActivator.getDefault().getTLAColorProvider();
        
        WordRule rule = new WordRule(new IWordDetector() {
            public boolean isWordStart(char c)
            {
                return Character.isJavaIdentifierStart(c);
            }

            public boolean isWordPart(char c)
            {
                return Character.isJavaIdentifierPart(c);
            }
        });
        Token keyword = new Token(new TextAttribute(provider.getColor(TLAColorProvider.KEYWORD), null, SWT.BOLD));
        Token comment = new Token(new TextAttribute(provider.getColor(TLAColorProvider.COMMENT)));
        Token string = new Token(new TextAttribute(provider.getColor(TLAColorProvider.STRING)));
        // add tokens for each reserved word
        for (int n = 0; n < TLACodeScanner.KEYWORDS.length; n++)
        {
            rule.addWord(TLACodeScanner.KEYWORDS[n], keyword);
        }
        setRules(new IRule[] { rule, new SingleLineRule("\\*", null, comment),
                new SingleLineRule("\"", "\"", string, '\\') 
                });

    }

}
