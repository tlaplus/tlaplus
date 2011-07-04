package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.ITypedRegion;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;

import tlc2.output.MP;

public class DummyListener implements ITLCOutputListener {

	// done has been called on the parser
	private boolean done = false;
	
	// parser has failed to parse test input
	private boolean garbage = false;
	
	// all typed regions recognized by the parser
	private List<ITypedRegion> regions = new ArrayList<ITypedRegion>();
	
	// all states found by the parser
	private List<TLCState> states = new ArrayList<TLCState>();

	public String getTLCOutputName() {
		// nop
		return "";
	}

	public void onOutput(ITypedRegion region, String text) {
		// a) just store the region
		this.regions.add(region);

		// b) convert to TLCState if TLCRegion
		if (region instanceof TLCRegion) {
			TLCRegion tlcRegion = (TLCRegion) region;
			int severity = tlcRegion.getSeverity();
			switch (severity) {
			case MP.STATE:
				TLCState state = TLCState.parseState(text, "bogusModelName");
				this.states.add(state);
				return;
			}
		}
		
		// c) unexpected content
		this.garbage  = true;
	}

	public void onDone() {
		this.done = true;
	}

	public void onNewSource() {
		// nop
	}

	/**
	 * @return the done
	 */
	public boolean isDone() {
		return done;
	}

	/**
	 * @return the garbage
	 */
	public boolean hasGarbage() {
		return garbage;
	}
	
	/**
	 * @return the regions
	 */
	public List<ITypedRegion> getRegions() {
		return regions;
	}

	/**
	 * @return the states
	 */
	public List<TLCState> getStates() {
		return states;
	}
}
