package org.lamport.tla.toolbox.tool.tlc.output;

import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
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
    public static final String COVERAGE_START = "__tlc_coverage_start"; //$NON-NLS-1$
    public static final String COVERAGE_END = "__tlc_coverage_end"; //$NON-NLS-1$
    public static final String INIT_END = "__tlc_init_end"; //$NON-NLS-1$
    public static final String INIT_START = "__tlc_init_start"; //$NON-NLS-1$
    public static final String CHECKPOINT_START = "__tlc_checkpoint_start"; //$NON-NLS-1$
    public static final String CHECKPOINT_END = "__tlc_checkpoint_end"; //$NON-NLS-1$
    public static final String OUTPUT = "__tlc_output"; //$NON-NLS-1$
    public static final String PROGRESS = "__tlc_progress"; //$NON-NLS-1$

    public static final String DEFAULT_CONTENT_TYPE = OUTPUT;
    public static final String[] CONTENT_TYPES = new String[] { COVERAGE_START, COVERAGE_END, INIT_START,
            INIT_END, OUTPUT, PROGRESS };

    // coverage
    private IToken coverageStart = new Token(COVERAGE_START);
    private IToken coverageEnd = new Token(COVERAGE_END);

    // status of TLC, computing init states
    private IToken initStart = new Token(INIT_START);
    // status of TLC, init states computed
    private IToken initEnd = new Token(INIT_END);
    // status of TLC, starting chekpointing
    private IToken checkpointStart = new Token(CHECKPOINT_START);
    // status of TLC, finished chekpointing
    private IToken checkpointEnd = new Token(CHECKPOINT_END);
    // intermediate progress
    private IToken progress = new Token(PROGRESS);

    public LogPartitionTokenScanner()
    {
        Vector rules = new Vector();

        // output produced by the print statements
        // IToken output = new Token(OUTPUT);

        rules.add(new EndOfLineRule("The coverage statistics :", coverageStart));
        rules.add(new EndOfLineRule("End of statistics.", coverageEnd));
        rules.add(new EndOfLineRule("Progress(", progress));
        rules.add(new EndOfLineRule("Finished computing initial states:", initEnd));
        rules.add(new EndOfLineRule("Computing initial states...", initStart));
        rules.add(new EndOfLineRule("Checkpointing of run ", checkpointStart));
        rules.add(new EndOfLineRule("Checkpointing completed.", checkpointEnd));

        setPredicateRules((IPredicateRule[]) rules.toArray(new IPredicateRule[rules.size()]));

        // output is default
        setDefaultReturnToken(new Token(DEFAULT_CONTENT_TYPE));
    }

    public IToken nextToken()
    {
        return super.nextToken();
    }

    
    public static IToken[] mergeCoverage(ITypedRegion coverageStart, ITypedRegion coverageEnd)
    {
        Assert.isNotNull(coverageStart);
        Assert.isNotNull(coverageEnd);
        
        
        return null;
    }
    
    

}
