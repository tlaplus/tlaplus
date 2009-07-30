package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Vector;

import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

/**
 * Partitioning of the TLC output
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TagBasedTLCOutputTokenScanner extends RuleBasedPartitionScanner
{
    public final static String RULE_DELIM = "@!@!@";
    public final static String RULE_START = RULE_DELIM + "STARTMSG"; 
    public final static String RULE_END = RULE_DELIM + "ENDMSG";
    
    public static final String TLA_PARTITIONING = "__tlc_output_partitioning"; //$NON-NLS-1$

    public static final String OUTPUT = "__tlc_output"; //$NON-NLS-1$
    public static final String TAG_OPEN = "__tlc_tag_open"; 
    public static final String TAG_CLOSED = "__tlc_tag_closed"; 
    public static final String TAG = "__tlc_tag";

    public static final String DEFAULT_CONTENT_TYPE = OUTPUT;
    public static final String[] CONTENT_TYPES = new String[] { OUTPUT, TAG_OPEN, TAG_CLOSED, TAG };

    public TagBasedTLCOutputTokenScanner()
    {
        Vector rules = new Vector();

        rules.add(new SingleLineRule(RULE_START, RULE_DELIM, new Token(TAG_OPEN)));
        rules.add(new SingleLineRule(RULE_END, RULE_DELIM, new Token(TAG_CLOSED)));
        
        // add the rules
        setPredicateRules((IPredicateRule[]) rules.toArray(new IPredicateRule[rules.size()]));

        // output is default
        setDefaultReturnToken(new Token(DEFAULT_CONTENT_TYPE));
    }
}
