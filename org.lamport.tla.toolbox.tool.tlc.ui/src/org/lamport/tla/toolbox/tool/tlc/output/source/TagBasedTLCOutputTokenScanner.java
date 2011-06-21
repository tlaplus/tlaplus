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
    private final static String HEAD_DELIM = "@!@!@";
    private final static String TAIL_DELIM = "";
    private final static String RULE_START = HEAD_DELIM + "STARTMSG";
    private final static String RULE_END = HEAD_DELIM + "ENDMSG";

    public static final String TAG_OPEN = "__tlc_tag_open";
    public static final String TAG_CLOSED = "__tlc_tag_closed";
    public static final String DEFAULT_CONTENT_TYPE = "__tlc_output";

    public static final String[] CONTENT_TYPES = new String[] { TAG_OPEN, TAG_CLOSED, DEFAULT_CONTENT_TYPE };

    public TagBasedTLCOutputTokenScanner()
    {
        Vector<SingleLineRule> rules = new Vector<SingleLineRule>();

        rules.add(new SingleLineRule(RULE_START, TAIL_DELIM + "\n", new Token(TAG_OPEN)));
        rules.add(new SingleLineRule(RULE_END, TAIL_DELIM + "\n", new Token(TAG_CLOSED)));

        // add the rules
        setPredicateRules((IPredicateRule[]) rules.toArray(new IPredicateRule[rules.size()]));

        // output is default
        setDefaultReturnToken(new Token(DEFAULT_CONTENT_TYPE));
    }
}
