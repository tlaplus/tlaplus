package org.lamport.tla.toolbox.tool.tlc.output.data;

import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;

/**
 * A presenter is responsible for the presentation of data handled by the {@link TLCModelLaunchDataProvider}
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface ITLCModelLaunchDataPresenter
{
    /* constants for the fields */
    public final static int USER_OUTPUT = 1;
    public final static int PROGRESS_OUTPUT = 2;
    public final static int START_TIME = 4;
    public final static int END_TIME = 8;
    public final static int COVERAGE_TIME = 16;
    public final static int COVERAGE = 32;
    public final static int PROGRESS = 64;
    public final static int ERRORS = 128;
    public final static int LAST_CHECKPOINT_TIME = 256;
    public final static int CURRENT_STATUS = 512;
    public final static int CONST_EXPR_EVAL_OUTPUT = 1024;
    public final static int FINGERPRINT_COLLISION_PROBABILITY = 2048;

    public final static int[] ALL_FIELDS = { USER_OUTPUT, PROGRESS_OUTPUT, START_TIME, END_TIME, LAST_CHECKPOINT_TIME,
            COVERAGE_TIME, COVERAGE, PROGRESS, ERRORS, CONST_EXPR_EVAL_OUTPUT, FINGERPRINT_COLLISION_PROBABILITY };

    /**
     * Retrieves the model 
     */
    public ILaunchConfigurationWorkingCopy getConfig();

    /**
     * Inform the presenter about the data changes
     * @param dataProvider data source
     * @param fieldId id of the changed field
     */
    public void modelChanged(final TLCModelLaunchDataProvider dataProvider, final int fieldId);
}
