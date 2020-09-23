package tlc2;

/**
 * Encapsulates settings related to dump files.
 * Should be rewritten as a record once that feature is main-lined.
 */
public class DumpFileOptions {
	/**
	 * Whether dump file output should be colorized.
	 */
	public boolean colorize;
	
	/**
	 * Whether dump file output should include action labels.
	 */
	public boolean actionLabels;
	
	/**
	 * Whether dump file output should include snapshots.
	 */
	public boolean snapshot;
	
	/**
	 * Creates a new DumpFileOptions instance.
	 * @param colorize Whether dump file output should be colorized.
	 * @param actionLabels Whether dump file output should include action labels.
	 * @param snapshot Whether dump file output should include snapshots.
	 */
	public DumpFileOptions(boolean colorize, boolean actionLabels, boolean snapshot)
	{
		this.colorize = colorize;
		this.actionLabels = actionLabels;
		this.snapshot = snapshot;
	}
}
