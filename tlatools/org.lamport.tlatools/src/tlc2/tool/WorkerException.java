// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:45 PST by lamport  
//      modified on Wed Dec  5 15:35:42 PST 2001 by yuanyu   

package tlc2.tool;

import tlc2.output.EC;
import util.Assert.TLCRuntimeException;

public class WorkerException extends Exception {

	// Keep the UID used by workers that predate the error code field.
	private static final long serialVersionUID = -8540165108045810212L;

	private final int errorCode;

	public TLCState state1;
	public TLCState state2;
	public boolean keepCallStack;

	public WorkerException(String msg) {
		this(msg, null, null, false);
	}

	public WorkerException(String msg, TLCState s1, TLCState s2, boolean keep) {
		this(EC.GENERAL, msg, s1, s2, keep);
	}

	public WorkerException(int errorCode, String msg, TLCState s1, TLCState s2, boolean keep) {
		super(msg);
		this.errorCode = errorCode;
		this.state1 = s1;
		this.state2 = s2;
		this.keepCallStack = keep;
	}

	public WorkerException(String msg, Throwable cause, TLCState s1, TLCState s2, boolean keep) {
		super(msg, cause);
		this.errorCode = EC.GENERAL;
		this.state1 = s1;
		this.state2 = s2;
		this.keepCallStack = keep;
	}

	public int getErrorCode() {
		if (errorCode != EC.NO_ERROR && errorCode != EC.GENERAL) {
			return errorCode;
		}
		// The worker may omit a specific code while still carrying a typed cause.
		final Throwable cause = getCause();
		final int code;
		if (cause instanceof EvalException) {
			code = ((EvalException) cause).getErrorCode();
		} else if (cause instanceof TLCRuntimeException) {
			code = ((TLCRuntimeException) cause).errorCode;
		} else {
			return EC.GENERAL;
		}
		return code == EC.NO_ERROR ? EC.GENERAL : code;
	}
}
