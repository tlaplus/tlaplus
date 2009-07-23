package org.lamport.tla.toolbox.tool.tlc.ui.output;

import java.util.Vector;

import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

/**
 * Partitioning of the TLC output
 * @author Simon Zambrovski
 * @version $Id$
 */
public class LogPartitionTokenScanner extends RuleBasedPartitionScanner
{

    public static final String TLA_PARTITIONING = "__tlc_output_partitioning"; //$NON-NLS-1$
    
    
    public static final String COVERAGE = "__tlc_coverage"; //$NON-NLS-1$
    public static final String INIT_END = "__tlc_init_end"; //$NON-NLS-1$
    public static final String INIT_START = "__tlc_init_start"; //$NON-NLS-1$
    public static final String OUTPUT = "__tlc_output"; //$NON-NLS-1$
    public static final String PROGRESS = "__tlc_progress"; //$NON-NLS-1$
    
    public static final String DEFAULT_CONTENT_TYPE = OUTPUT; 
    public static final String[] CONTENT_TYPES = new String[] { COVERAGE, INIT_START, INIT_END, OUTPUT, PROGRESS };

    public LogPartitionTokenScanner()
    {
        Vector rules = new Vector();

        // coverage
        IToken coverage = new Token(COVERAGE);

        // status of TLC, init stated computed
        IToken init_end = new Token(INIT_END);
        // status of TLC, computing init stated
        IToken init_start = new Token(INIT_START);

        // intermediate progress
        IToken progress = new Token(PROGRESS);
        
        // output produced by the print statements
        // IToken output = new Token(OUTPUT);

        rules.add(new MultiLineRule("The coverage statistics", "End of statistics", coverage, (char) 0, false));
        rules.add(new SingleLineRule("Progress(", "", progress));
        rules.add(new SingleLineRule("Finished computing initial states:", "", init_end));
        rules.add(new SingleLineRule("Computing initial states...", "", init_start));
        
        
        setPredicateRules((IPredicateRule[]) rules.toArray(new IPredicateRule[rules.size()]));

        // output is default
        setDefaultReturnToken(new Token(DEFAULT_CONTENT_TYPE));
    }

    public IToken nextToken()
    {
        return super.nextToken();
    }

}
