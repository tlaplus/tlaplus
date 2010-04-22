package org.lamport.tla.toolbox.tool.prover.ui.output;

import java.util.ArrayList;

import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

/**
 * This class is used to partition the output of the TLAPM
 * into useful regions. It does so by defining rules
 * for partitions.
 * 
 * Initially, it will only define a rule to look for strings
 * of the form
 * 
 * @!!<text>@!!
 * 
 * Currently, only proof obligation status reports appear between tags
 * @!!.
 * 
 * @author Daniel Ricketts
 *
 */
public class TagBasedTLAPMOutputTokenScanner extends RuleBasedPartitionScanner
{
    public static final String BEGIN_TAG = "@!!";
    public static final String END_TAG = "@!!";

    /**
     * The content type for obligation status reports.
     */
    public static final String OBLIGATION_STATUS = "_obligation_status";
    /**
     * The default content type.
     */
    public static final String DEFAULT_CONTENT_TYPE = "__tlapm_output";

    public static final String[] CONTENT_TYPES = new String[] { OBLIGATION_STATUS, DEFAULT_CONTENT_TYPE };

    public TagBasedTLAPMOutputTokenScanner()
    {
        ArrayList rules = new ArrayList();

        /*
         * The token passed in to the rule constructor contains the content
         * type for the token returned when the text being scanned contains
         * a string following the rule.
         */
        rules.add(new SingleLineRule(BEGIN_TAG, END_TAG, new Token(OBLIGATION_STATUS)));

        // add the rules
        setPredicateRules((IPredicateRule[]) rules.toArray(new IPredicateRule[rules.size()]));

        // output is default
        setDefaultReturnToken(new Token(DEFAULT_CONTENT_TYPE));
    }

}
