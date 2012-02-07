// Copyright (c) Feb 6, 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Vector;

import org.eclipse.jface.text.Document;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;

/**
 * @author Markus Alexander Kuppe
 */
/**
 * @author Markus Alexander Kuppe
 */
/**
 * @author Markus Alexander Kuppe
 */
public class Bug267Listener extends TLCModelLaunchDataProvider implements
		ITLCOutputListener {
	
	public Bug267Listener() {
		super(null);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider#getModelName()
	 */
	protected String getModelName() {
		return getTLCOutputName();
	}
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider#initialize()
	 */
	protected void initialize() {
		isDone = false;
		isTLCStarted = false;
		errors = new Vector<TLCError>();
		lastDetectedError = null;
		coverageInfo = new Vector<CoverageInformationItem>();
		progressInformation = new Vector<StateSpaceInformationItem>();
		startTime = 0;
		startTimestamp = Long.MIN_VALUE;
		finishTimestamp = Long.MIN_VALUE;
		lastCheckpointTimeStamp = Long.MIN_VALUE;
		coverageTimestamp = "";
		setCurrentStatus(NOT_RUNNING);
		setFingerprintCollisionProbability("");
		progressOutput = new Document(NO_OUTPUT_AVAILABLE);
		userOutput = new Document(NO_OUTPUT_AVAILABLE);
		constantExprEvalOutput = "";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider#getTLCOutputName()
	 */
	public String getTLCOutputName() {
		return "Bug267";
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider#createError(org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion, java.lang.String)
	 */
	protected TLCError createError(TLCRegion tlcRegion, String message) {
		// the root of the error trace
		return new TLCError();
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider#connectToSourceRegistry()
	 */
	public void connectToSourceRegistry() {
		// intentionally noop
	}
}
