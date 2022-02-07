// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:35 PST by lamport 
//      modified on Sat Feb 17 12:07:55 PST 2001 by yuanyu 

package tlc2.tool;

// TLCStateInfo is largely obsolete and should be replaced in favor of
// TLCStateMutExt, which has support for storing the predecessor, action,
// and level (stateNum), but doesn't have to be created after the fact,
// that is from an existing TLCState trace, but gets created by Tool/
// TLCTrace. However, TLCStateInfo is used in too many places, which makes
// this particular refactoring too expensive right now.  Also, TLCStateMutExt
// doesn't get used in throughput-optimized BFS search (unless TLC runs in
// '-debugger' mode).
public class TLCStateInfo {
  private static final String INITIAL_PREDICATE_NO_ANGLE_BRACKET = "Initial predicate";

  public static final String INITIAL_PREDICATE = "<" + INITIAL_PREDICATE_NO_ANGLE_BRACKET + ">";
  
  public TLCStateInfo predecessorState;
  public long stateNumber;
  public Object info;
  public final TLCState state;
  public Long fp;

  public TLCStateInfo(final TLCState state) {
	this.state = state;
	this.stateNumber = state.getLevel();
	
	if (state.hasAction()) {
		// In simulation mode or when TLC runs with "-debugger", states have the Action
		// attached.
		this.info = toInfo(state.isInitial(), state.getAction());
	} else {
		// Traditionally (hail legacy), the name and location of the initial predicate is unknown.
		// See e.g. https://github.com/tlaplus/tlaplus/issues/305
		this.info = INITIAL_PREDICATE;
	}
  }

  public TLCStateInfo(final TLCState state, final Action action) {
	this.state = state;
	this.stateNumber = state.getLevel();
	
	this.info = toInfo(state.isInitial(), action);
  }
  
  private static String toInfo(final boolean isInitial, final Action a) {
	  if (isInitial && !a.isNamed()) {
		  // It is possible for an action to have no name, yet to have a location. Instead
		  // of showing <Action loc ...>, we show <Initial Predicate loc...> for legacy
	      // reasons.
		  return a.getLocation(INITIAL_PREDICATE_NO_ANGLE_BRACKET);
	  }
	  return a.getLocation();
  }
  
  // Legacy (DFID & MP)
  public TLCStateInfo(final TLCState state, final int stateOrdinal) {
		this.state = state;
		this.stateNumber = stateOrdinal;
		this.info = "";
  }
  
  // AliasTLCStateInfo
  protected TLCStateInfo(final TLCState s, final TLCStateInfo info) {
	  this.state = s;
	  this.info = info.info;
	  this.stateNumber = info.stateNumber;
	  this.fp = info.fp;
  }

  public final long fingerPrint() {
	  if (fp == null) {
		  fp = this.state.fingerPrint();
	  }
	  return fp.longValue();
  }

  public final String toString() {
    return this.state.toString();
  }
  
  public boolean equals(Object other) {
	  if (other instanceof TLCStateInfo) {
		  TLCStateInfo sinfo = (TLCStateInfo) other;
		  return this.state.equals(sinfo.state);
	  } else if (other instanceof TLCState) {
		  TLCState state = (TLCState) other;
		  return this.state.equals(state);
	  }
	  return false;
  }

  public int hashCode() {
	  return this.state.hashCode();
  }

  public TLCState getOriginalState() {
	return state;
  }
  
  public Action getAction() {
	  if (state.hasAction()) {
		  return state.getAction();
	  }
	  return Action.UNKNOWN;
  }
}
