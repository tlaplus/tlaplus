package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.text.NumberFormat;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
	 * True if this is the most recent/up-to-date SSII holding the newest
	 * values.
	 */
	private boolean isMostRecent = true;

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
	
	private StateSpaceInformationItem(Date time, long foundStates, long distinctStates) {
		this(time, 0, foundStates, distinctStates, distinctStates, 0, 0);
	}

	private StateSpaceInformationItem(Date time, long distinctStates) {
		this(time, distinctStates, distinctStates);
	}
	
	private StateSpaceInformationItem(long foundStates, long distinctStates) {
		this(new Date(), 0, foundStates, distinctStates, distinctStates, 0, 0);
	}

	private StateSpaceInformationItem(long distinctStates) {
		this(distinctStates, distinctStates);
	}
 	
   /**
	 * @return the isMostRecent
	 */
	public boolean isMostRecent() {
		return isMostRecent;
	}

	/**
	 * @param isMostRecent the isMostRecent to set
	 */
	public void setMostRecent(boolean isMostRecent) {
		this.isMostRecent = isMostRecent;
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
		final String OB = "(";
		final String AT = ") at ";
		final String COLON = ": ";
		final String GENERATED = " states generated (";
		final String SPM = " s/min), ";
		final String DISTINCT = " distinct states found (";
		final String DISTINCT_SPM = " ds/min), ";
		final String LEFT = " states left on queue.";

		// validated output is properly formatted by trying to find the known
		// parts at expected locations.
		int[] i = { outputMessage.indexOf(OB), outputMessage.indexOf(AT),
				outputMessage.indexOf(COLON), outputMessage.indexOf(GENERATED),
				outputMessage.indexOf(SPM), outputMessage.indexOf(DISTINCT),
				outputMessage.indexOf(DISTINCT_SPM),
				outputMessage.indexOf(LEFT) };

		for (int j = 0; j < i.length; j++) {
			if (i[j] == -1) {
				return parseOld(outputMessage);
			}
		}

		// assuming the previous check suffices, it should now be possible to
		// parse the string back to its real types
		try {
			final Date time = SDF.parse(outputMessage.substring(
					i[1] + AT.length(), i[2]));

			final NumberFormat nf = NumberFormat.getNumberInstance();
			
			final long diameter = Long.parseLong(outputMessage.substring(i[0]
					+ OB.length(), i[1]));
			final long foundStates = Long.parseLong(outputMessage.substring(
					i[2] + COLON.length(), i[3]));
			final long statesPerMinute = nf.parse(outputMessage
					.substring(i[3] + GENERATED.length(), i[4]).replace(",", "")).longValue();

			final long distinctStates = Long.parseLong(outputMessage.substring(
					i[4] + SPM.length(), i[5]));
			final long distinctStatesPerMinute = nf.parse(outputMessage
					.substring(i[5] + DISTINCT.length(), i[6]).replace(",", "")).longValue();

			final long leftStates = Long.parseLong(outputMessage.substring(i[6]
					+ DISTINCT_SPM.length(), i[7]));

			return new StateSpaceInformationItem(time, diameter, foundStates,
					distinctStates, leftStates, statesPerMinute,
					distinctStatesPerMinute);
		} catch (NumberFormatException e) {
			TLCUIActivator.getDefault().logError("Error reading progress information", e);
		} catch (ParseException e) {
			TLCUIActivator.getDefault().logError("Error reading progress information", e);
		}
		return null;
	}
	
	public static StateSpaceInformationItem parseInit(final String outputMessage) {
		// Handles  EC.TLC_INIT_GENERATED1 and EC.TLC_INIT_GENERATED2.-
		// From MP#getMessage:
        //   b.append("Finished computing initial states: %1% distinct state%2% generated.");
        //   b.append("Finished computing initial states: %1% state%2% generated, with %3% of them distinct.");

		// Legacy pattern without date.
		Pattern pattern = Pattern.compile("^Finished computing initial states: ([0-9]+) distinct state[s]* generated.$");
		Matcher matcher = pattern.matcher(outputMessage);
		if (matcher.find()) {
			final long distinctStates = Long.parseLong(matcher.group(1));
			return new StateSpaceInformationItem(distinctStates);
		}

		pattern = Pattern.compile(
				"^Finished computing initial states: ([0-9]+) states generated, with ([0-9]+) of them distinct.$");
		matcher = pattern.matcher(outputMessage);
		if (matcher.find()) {
			final long foundStates = Long.parseLong(matcher.group(1));
			final long distinctStates = Long.parseLong(matcher.group(2));
			return new StateSpaceInformationItem(foundStates, distinctStates);
		}
		
		// New patterns with date.
		pattern = Pattern.compile("^Finished computing initial states: ([0-9]+) distinct state[s]* generated at (.*).$");
		matcher = pattern.matcher(outputMessage);
		if (matcher.find()) {
			final long distinctStates = Long.parseLong(matcher.group(1));
			final Date date = parseDate(matcher.group(2));
			return new StateSpaceInformationItem(date, distinctStates);
		}

		pattern = Pattern.compile(
				"^Finished computing initial states: ([0-9]+) states generated, with ([0-9]+) of them distinct at (.*).$");
		matcher = pattern.matcher(outputMessage);
		if (matcher.find()) {
			final long foundStates = Long.parseLong(matcher.group(1));
			final long distinctStates = Long.parseLong(matcher.group(2));
			final Date date = parseDate(matcher.group(3));
			return new StateSpaceInformationItem(date, foundStates, distinctStates);
		}
		return null;
	}
	
	private static Date parseDate(String str) {
		try {
			return SDF.parse(str);
		} catch (ParseException e) {
			return new Date();
		}
	}

	/**
     * @param outputMessage
     * @return
     */
	public static StateSpaceInformationItem parseOld(String outputMessage) {
	    final String OB = "(";
	    final String AT = ") at ";
	    final String COLON = ": ";
	    final String GENERATED = " states generated, ";
	    final String DISTINCT = " distinct states found, ";
	    final String LEFT = " states left on queue.";
	    
		// TODO support formats of SIMULATOR and DFID
		// "Progress(23) at 2009-08-07 08:20:02: 1604317 states generated, 421523 distinct states found, 109513 states left on queue."
		int[] i = { outputMessage.indexOf(OB), outputMessage.indexOf(AT),
				outputMessage.indexOf(COLON), outputMessage.indexOf(GENERATED),
				outputMessage.indexOf(DISTINCT), outputMessage.indexOf(LEFT) };

		for (int j = 0; j < i.length; j++) {
			if (i[j] == -1) {
				TLCUIActivator.getDefault().logError("Error reading progress information",
						new IllegalArgumentException(outputMessage
								+ " is in wrong format"));
				return null;
			}
		}

		try {
			return new StateSpaceInformationItem(SDF.parse(outputMessage
					.substring(i[1] + AT.length(), i[2])),
					Long.parseLong(outputMessage.substring(i[0] + OB.length(),
							i[1])), Long.parseLong(outputMessage.substring(i[2]
							+ COLON.length(), i[3])),
					Long.parseLong(outputMessage.substring(
							i[3] + GENERATED.length(), i[4])),
					Long.parseLong(outputMessage.substring(
							i[4] + DISTINCT.length(), i[5])), 0, 0);
		} catch (NumberFormatException e) {
			TLCUIActivator.getDefault().logError("Error reading progress information", e);
		} catch (ParseException e) {
			TLCUIActivator.getDefault().logError("Error reading progress information", e);
		}
		return null;
	}

	public final static SimpleDateFormat SDF = new SimpleDateFormat(
			"yyyy-MM-dd HH:mm:ss");

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (int) (diameter ^ (diameter >>> 32));
		result = prime * result + (int) (distinctStates ^ (distinctStates >>> 32));
		result = prime * result + (int) (foundStates ^ (foundStates >>> 32));
		result = prime * result + (int) (leftStates ^ (leftStates >>> 32));
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		StateSpaceInformationItem other = (StateSpaceInformationItem) obj;
		if (diameter != other.diameter)
			return false;
		if (distinctStates != other.distinctStates)
			return false;
		if (foundStates != other.foundStates)
			return false;
		if (leftStates != other.leftStates)
			return false;
		return true;
	}
}
