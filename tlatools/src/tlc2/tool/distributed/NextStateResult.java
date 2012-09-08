// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed;

import java.io.Serializable;

import tlc2.tool.TLCStateVec;
import tlc2.util.LongVec;

@SuppressWarnings("serial")
public class NextStateResult implements Serializable {

	private final long computationTime;
	private final long statesComputed;
	private final TLCStateVec[] nextStates;
	private final LongVec[] nextFingerprints;
	
	public NextStateResult(TLCStateVec[] nextStates, LongVec[] nextFingerprints, 
			long computationTime, long statesComputed) {
		this.nextStates = nextStates;
		this.nextFingerprints = nextFingerprints;
		this.computationTime = computationTime;
		this.statesComputed = statesComputed;
	}
	
	public long getStatesComputedDelta() {
		return statesComputed - nextStates.length;
	}

	public long getComputationTime() {
		return computationTime;
	}

	public LongVec[] getNextFingerprints() {
		return nextFingerprints;
	}

	public TLCStateVec[] getNextStates() {
		return nextStates;
	}
}
