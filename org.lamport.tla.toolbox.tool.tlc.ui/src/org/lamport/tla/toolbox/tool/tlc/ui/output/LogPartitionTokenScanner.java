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
    public static final String CHECKPOINT_START = "__tlc_checkpoint_start"; //$NON-NLS-1$
    public static final String CHECKPOINT_END = "__tlc_checkpoint_end"; //$NON-NLS-1$
    public static final String OUTPUT = "__tlc_output"; //$NON-NLS-1$
    public static final String PROGRESS = "__tlc_progress"; //$NON-NLS-1$
    
    public static final String DEFAULT_CONTENT_TYPE = OUTPUT; 
    public static final String[] CONTENT_TYPES = new String[] { COVERAGE, INIT_START, INIT_END, OUTPUT, PROGRESS };

    public LogPartitionTokenScanner()
    {
        Vector rules = new Vector();

        // coverage
        IToken coverage = new Token(COVERAGE);

        // status of TLC, computing init states
        IToken initStart = new Token(INIT_START);
        // status of TLC, init states computed
        IToken initEnd = new Token(INIT_END);
        // status of TLC, starting chekpointing
        IToken checkpointStart = new Token(CHECKPOINT_START);
        // status of TLC, finished chekpointing
        IToken checkpointEnd = new Token(CHECKPOINT_END);
        // intermediate progress
        IToken progress = new Token(PROGRESS);
        
        // output produced by the print statements
        // IToken output = new Token(OUTPUT);

        rules.add(new MultiLineRule("The coverage statistics :", "End of statistics.", coverage, (char) 0, false));
        rules.add(new SingleLineRule("Progress(", " left on queue.", progress));
        rules.add(new SingleLineRule("Finished computing initial states:", "state generated.", initEnd));
        rules.add(new SingleLineRule("Computing initial states...", "", initStart));
        rules.add(new SingleLineRule("Checkpointing of run ", "", checkpointStart));
        rules.add(new SingleLineRule("Checkpointing completed.", "", checkpointEnd));
        
        
        setPredicateRules((IPredicateRule[]) rules.toArray(new IPredicateRule[rules.size()]));

        // output is default
        setDefaultReturnToken(new Token(DEFAULT_CONTENT_TYPE));
    }

    public IToken nextToken()
    {
        return super.nextToken();
    }

}
