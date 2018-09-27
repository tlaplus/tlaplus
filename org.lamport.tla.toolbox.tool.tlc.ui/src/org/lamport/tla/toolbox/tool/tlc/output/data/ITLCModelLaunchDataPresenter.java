package org.lamport.tla.toolbox.tool.tlc.output.data;

/**
 * A presenter is responsible for the presentation of data handled by the {@link TLCModelLaunchDataProvider}
 * @author Simon Zambrovski
 */
public interface ITLCModelLaunchDataPresenter
{
    /* constants for the fields */
	public final static int USER_OUTPUT = 1;
	public final static int PROGRESS_OUTPUT = USER_OUTPUT << 1;
	public final static int START_TIME = PROGRESS_OUTPUT << 1;
	public final static int END_TIME = START_TIME << 1;
	public final static int COVERAGE_TIME = END_TIME << 1;
	public final static int COVERAGE = COVERAGE_TIME << 1;
	public final static int COVERAGE_END = COVERAGE << 1;
	public final static int PROGRESS = COVERAGE_END << 1;
	public final static int ERRORS = PROGRESS << 1;
	public final static int LAST_CHECKPOINT_TIME = ERRORS << 1;
	public final static int CURRENT_STATUS = LAST_CHECKPOINT_TIME << 1;
	public final static int CONST_EXPR_EVAL_OUTPUT = CURRENT_STATUS << 1;
	public final static int FINGERPRINT_COLLISION_PROBABILITY = CONST_EXPR_EVAL_OUTPUT << 1;
	public static final int DISTRIBUTED_SERVER_RUNNING = FINGERPRINT_COLLISION_PROBABILITY << 1;
	public static final int DISTRIBUTED_WORKER_REGISTERED = DISTRIBUTED_SERVER_RUNNING << 1;
	public static final int TLC_MODE = DISTRIBUTED_WORKER_REGISTERED << 1;

	public final static int[] ALL_FIELDS = { USER_OUTPUT, PROGRESS_OUTPUT, START_TIME, END_TIME, LAST_CHECKPOINT_TIME,
			COVERAGE_TIME, COVERAGE, COVERAGE_END, PROGRESS, ERRORS, CONST_EXPR_EVAL_OUTPUT,
			FINGERPRINT_COLLISION_PROBABILITY, DISTRIBUTED_SERVER_RUNNING, DISTRIBUTED_WORKER_REGISTERED, TLC_MODE };

    /**
     * Inform the presenter about the data changes
     * @param dataProvider data source
     * @param fieldId id of the changed field
     */
    public void modelChanged(final TLCModelLaunchDataProvider dataProvider, final int fieldId);
}
