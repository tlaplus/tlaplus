// Copyright (c) Feb 6, 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import org.easymock.EasyMock;
import org.eclipse.core.resources.IFile;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.text.Document;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformation;
import org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;

public class Bug267Listener extends TLCModelLaunchDataProvider implements
		ITLCOutputListener {
	
	public Bug267Listener() {
		super(new DummyModel());
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider#getModelName()
	 */
	protected String getModelName() {
		return "Bug267";
	}
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider#initialize()
	 */
	protected void initialize() {
		isDone = false;
		isTLCStarted = false;
		errors = new Vector<TLCError>();
		lastDetectedError = null;
		coverageInfo = new CoverageInformation();
		progressInformation = new Vector<StateSpaceInformationItem>();
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
	 * @see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider#getModel()
	 */
	public Model getModel() {
		return null;
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
	public boolean connectToSourceRegistry() {
		return false;
	}
	
	private static class DummyModel extends Model {

		DummyModel() {
			super(EasyMock.createNiceMock(ILaunchConfiguration.class));
		}

		public String getName() {
			// Stop super from delegating to ILC
			return "Bug267Listener";
		}

		@Override
		public List<IFile> getSavedTLAFiles() {
			return new ArrayList<IFile>();
		}
	}
}
