package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

/**
 * Partition token scanner
 *  
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAPartitionScanner extends RuleBasedPartitionScanner implements IPartitionTokenScanner
{
    public static final String TLA_PARTITIONING = "__tla_partitioning"; //$NON-NLS-1$
    public final static String TLA_MULTILINE_COMMENT = "__tla_multiline_comment"; //$NON-NLS-1$

    /**
     * supported partition types
     */
    public static final String[] TLA_PARTITION_TYPES = new String[] { TLA_MULTILINE_COMMENT };

    /**
     * Constructor
     */
    public TLAPartitionScanner()
    {
        super();
        setPredicateRules(new IPredicateRule[]{new MultiLineRule("(*", "*)", new Token(TLA_MULTILINE_COMMENT), (char) 0, true)});
    }
}
