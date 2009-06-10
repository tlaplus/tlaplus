package org.lamport.tla.toolbox.editor.basic;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

/**
 * Token partition scanner
 *  
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAPartitionScanner extends RuleBasedPartitionScanner implements IPartitionTokenScanner
{
    public static final String TLA_PARTITIONING = "__tla_partitioning"; //$NON-NLS-1$
    public final static String TLA_COMMENT = "__tla_comment"; //$NON-NLS-1$
    public final static String TLA_MULTILINE_COMMENT = "__tla_multiline_comment"; //$NON-NLS-1$
    public final static String PCAL_ALGORITHM = "__pcal_algorithm"; //$NON-NLS-1$
    public final static String TLA_RESERVED_WORD = "__tla_reserved"; //$NON-NLS-1$
    public final static String TLA_OPERATOR = "__tla_operator"; //$NON-NLS-1$

    /**
     * 
     */
    public static final String[] TLA_PARTITION_TYPES = new String[] { TLA_MULTILINE_COMMENT, TLA_COMMENT };

    /**
     * Constructor
     */
    public TLAPartitionScanner()
    {
        super();

        IToken multilineComment = new Token(TLA_MULTILINE_COMMENT);
        IToken comment = new Token(TLA_COMMENT);

        List rules = new ArrayList();

        // Add rule for single line comments.
        rules.add(new EndOfLineRule("\\*", comment)); //$NON-NLS-1$

        /*
        // Add rule for strings and character constants.
        rules.add(new SingleLineRule("\"", "\"", Token.UNDEFINED, '\\')); //$NON-NLS-2$ //$NON-NLS-1$
        rules.add(new SingleLineRule("'", "'", Token.UNDEFINED, '\\')); //$NON-NLS-2$ //$NON-NLS-1$
         */

        // Add special case word rule.
        // rules.add(new WordPredicateRule(comment));
        // Add rules for multi-line comments.
        rules.add(new MultiLineRule("(*", "*)", multilineComment, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$

        IPredicateRule[] result = new IPredicateRule[rules.size()];
        rules.toArray(result);
        setPredicateRules(result);
    }

}
