package org.lamport.tla.toolbox.tool.tlc.ui.trace;

import java.io.File;
import java.io.IOException;

import org.lamport.tla.toolbox.util.RCPNameToFileIStream;

import tlc2.tool.TLCStateInfo;
import tlc2.tool.TLCTrace;
import tlc2.tool.Tool;
import tlc2.util.FP64;
import util.ToolIO;

public class TLCTraceFileModelProvider {

	private TLCStateInfo[] stateInfos;

	public TLCTraceFileModelProvider(final File specFile, final File traceFile) throws IOException {
		// static initializers
		FP64.Init(0); // TODO handle cases where FP64 has been initialized with > 0
		ToolIO.setUserDir(specFile.getParent());

		// setup tool
		String specName = stripOffExtension(specFile.getName());
		final Tool tool = new Tool(specFile.getParent(), specName, specName, new RCPNameToFileIStream(null));
		tool.init(true, null);
		tool.getImpliedInits(); // implied-inits to be checked
		tool.getImpliedActions(); // implied-actions to be checked
		tool.getActions(); // the sub-actions

		// recreate TLCTrace
		final TLCTrace trace = new TLCTrace(traceFile.getParent(), stripOffExtension(traceFile.getName()), tool);

		// process trace file
		stateInfos = trace.getTrace();
	}
	
	private String stripOffExtension(final String aFileName) {
		int lastIndexOf = aFileName.lastIndexOf(".");
		return aFileName.substring(0, lastIndexOf);
	}

	public TLCStateInfo[] getTrace() {
		return stateInfos;
	}
}
