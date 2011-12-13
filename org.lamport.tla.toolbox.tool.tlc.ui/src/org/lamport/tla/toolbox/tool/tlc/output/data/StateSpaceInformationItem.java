package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;

import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * Representation of the state space progress item 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StateSpaceInformationItem
{
    private Date time;
    /*
     * The number of states can exceed
     * the maximum int, so we use a long.
     */
    private long diameter;
    private long foundStates;
    private long distinctStates;
    private long leftStates;
	private long spm;
	private long distinctSPM;

    /**
	 * @param time
	 * @param diameter
	 * @param foundStates
	 * @param distinctStates
	 * @param leftStates
	 * @param spm
	 * @param distinctSPM
	 */
	private StateSpaceInformationItem(Date time, long diameter,
			long foundStates, long distinctStates, long leftStates, long spm,
			long distinctSPM) {
		super();
		this.time = time;
		this.diameter = diameter;
		this.foundStates = foundStates;
		this.distinctStates = distinctStates;
		this.leftStates = leftStates;
		this.spm = spm;
		this.distinctSPM = distinctSPM;
	}

	public final Date getTime() {
		return time;
	}

	public final void setTime(Date time) {
		this.time = time;
	}

	public final long getDiameter() {
		return diameter;
	}

	public final void setDiameter(long diameter) {
		this.diameter = diameter;
	}

	public final long getFoundStates() {
		return foundStates;
	}

	public final void setFoundStates(long foundStates) {
		this.foundStates = foundStates;
	}

	public final long getDistinctStates() {
		return distinctStates;
	}

	public final void setDistinctStates(int distinctStates) {
		this.distinctStates = distinctStates;
	}

	public final long getLeftStates() {
		return leftStates;
	}

	public final void setLeftStates(long leftStates) {
		this.leftStates = leftStates;
	}

	/**
	 * @return the spm
	 */
	public long getSpm() {
		return spm;
	}

	/**
	 * @return the distinctSPM
	 */
	public long getDistinctSPM() {
		return distinctSPM;
	}

	/**
	 * @param outputMessage
	 * @return
	 */
	// TODO support formats of SIMULATOR and DFID
	public static StateSpaceInformationItem parse(String outputMessage) {
		// validated output is properly formatted by trying to find the known
		// parts at expected locations.
		int[] i = { outputMessage.indexOf(OB), outputMessage.indexOf(AT),
				outputMessage.indexOf(COLON), outputMessage.indexOf(GENERATED),
				outputMessage.indexOf(SPM), outputMessage.indexOf(DISTINCT),
				outputMessage.indexOf(DISTINCT_SPM),
				outputMessage.indexOf(LEFT) };

		for (int j = 0; j < i.length; j++) {
			if (i[j] == -1) {
				TLCUIActivator.logError("Error reading progress information",
						new IllegalArgumentException(outputMessage
								+ " is in wrong format"));
				return null;
			}
		}

		// assuming the previous check suffices, it should now be possible to
		// parse the string back to its real types
		try {
			final Date time = SDF.parse(outputMessage.substring(
					i[1] + AT.length(), i[2]));

			final long diameter = Long.parseLong(outputMessage.substring(i[0]
					+ OB.length(), i[1]));
			final long foundStates = Long.parseLong(outputMessage.substring(
					i[2] + COLON.length(), i[3]));
			final long statesPerMinute = Long.parseLong(outputMessage
					.substring(i[3] + GENERATED.length(), i[4]));

			final long distinctStates = Long.parseLong(outputMessage.substring(
					i[4] + SPM.length(), i[5]));
			final long distinctStatesPerMinute = Long.parseLong(outputMessage
					.substring(i[5] + DISTINCT.length(), i[6]));

			final long leftStates = Long.parseLong(outputMessage.substring(i[6]
					+ DISTINCT_SPM.length(), i[7]));

			return new StateSpaceInformationItem(time, diameter, foundStates,
					distinctStates, leftStates, statesPerMinute,
					distinctStatesPerMinute);
		} catch (NumberFormatException e) {
			TLCUIActivator.logError("Error reading progress information", e);
		} catch (ParseException e) {
			TLCUIActivator.logError("Error reading progress information", e);
		}
		return null;
	}

	public final static SimpleDateFormat SDF = new SimpleDateFormat(
			"yyyy-MM-dd HH:mm:ss");

	public final static String OB = "(";
	public final static String AT = ") at ";
	public final static String COLON = ": ";
	public final static String GENERATED = " states generated (";
	public final static String SPM = " s/min), ";
	public final static String DISTINCT = " distinct states found (";
	public final static String DISTINCT_SPM = " ds/min), ";
	public final static String LEFT = " states left on queue.";

}
