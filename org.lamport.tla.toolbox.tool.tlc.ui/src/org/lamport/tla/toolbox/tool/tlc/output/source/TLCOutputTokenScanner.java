package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Vector;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

/**
 * Partitioning of the TLC output
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCOutputTokenScanner extends RuleBasedPartitionScanner
{

    public static final String TLA_PARTITIONING = "__tlc_output_partitioning"; //$NON-NLS-1$

    public static final String COVERAGE = "__tlc_coverage"; //$NON-NLS-1$
    public static final String COVERAGE_START = "__tlc_coverage_start"; //$NON-NLS-1$
    public static final String COVERAGE_END = "__tlc_coverage_end"; //$NON-NLS-1$
    public static final String INIT_END = "__tlc_init_end"; //$NON-NLS-1$
    public static final String INIT_START = "__tlc_init_start"; //$NON-NLS-1$
    public static final String CHECKPOINT_START = "__tlc_checkpoint_start"; //$NON-NLS-1$
    public static final String CHECKPOINT_END = "__tlc_checkpoint_end"; //$NON-NLS-1$
    public static final String OUTPUT = "__tlc_output"; //$NON-NLS-1$
    public static final String PROGRESS = "__tlc_progress"; //$NON-NLS-1$
    public static final String STARTED = "__tlc_started"; //$NON-NLS-1$
    public static final String FINISHED = "__tlc_finished"; //$NON-NLS-1$
    
    public static final String DEFAULT_CONTENT_TYPE = OUTPUT;
    public static final String[] CONTENT_TYPES = new String[] { COVERAGE_START, COVERAGE_END, INIT_START,
            INIT_END, OUTPUT, PROGRESS, STARTED, FINISHED };
    public TLCOutputTokenScanner()
    {
        Vector rules = new Vector();

        // coverage start
        rules.add(new EndOfLineRule("The coverage statistics :", new Token(COVERAGE_START)));
        // coverage end
        rules.add(new EndOfLineRule("End of statistics.", new Token(COVERAGE_END)));
        // intermediate progress
        rules.add(new EndOfLineRule("Progress", new Token(PROGRESS)));
        // status of TLC, init states computed
        rules.add(new EndOfLineRule("Finished computing initial states:", new Token(INIT_END)));
        // status of TLC, computing init states        
        rules.add(new EndOfLineRule("Computing initial states...", new Token(INIT_START)));
        // status of TLC, starting chekpointing
        rules.add(new EndOfLineRule("Checkpointing of run ", new Token(CHECKPOINT_START)));
        // status of TLC, finished chekpointing
        rules.add(new EndOfLineRule("Checkpointing completed.", new Token(CHECKPOINT_END)));
        // start
        rules.add(new EndOfLineRule("Starting...", new Token(STARTED)));
        // finish
        rules.add(new EndOfLineRule("Finished.", new Token(FINISHED)));
        // add the rules
        setPredicateRules((IPredicateRule[]) rules.toArray(new IPredicateRule[rules.size()]));

        // output is default
        setDefaultReturnToken(new Token(DEFAULT_CONTENT_TYPE));
    }
}
