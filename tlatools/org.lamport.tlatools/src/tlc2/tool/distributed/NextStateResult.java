// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed;

import tlc2.tool.TLCState;
import tlc2.util.LongVec;

import java.io.Serializable;
import java.util.ArrayList;

@SuppressWarnings("serial")
public class NextStateResult implements Serializable {

    private final long computationTime;
    private final long statesComputed;
    private final ArrayList<TLCState>[] nextStates;
    private final LongVec[] nextFingerprints;

    public NextStateResult(final ArrayList<TLCState>[] nextStates, final LongVec[] nextFingerprints,
                           final long computationTime, final long statesComputed) {
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

    public ArrayList<TLCState>[] getNextStates() {
        return nextStates;
    }
}
