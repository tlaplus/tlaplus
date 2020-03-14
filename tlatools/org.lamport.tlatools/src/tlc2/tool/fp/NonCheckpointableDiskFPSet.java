/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool.fp;

import java.io.IOException;
import java.rmi.RemoteException;

import tlc2.output.EC;
import tlc2.output.MP;

@SuppressWarnings("serial")
public abstract class NonCheckpointableDiskFPSet extends DiskFPSet {

	protected NonCheckpointableDiskFPSet(FPSetConfiguration fpSetConfig) throws RemoteException {
		super(fpSetConfig);
	}

	public void beginChkpt(String fname) throws IOException {
		MP.printWarning(EC.GENERAL, "Checkpointing is not implemented for " + getClass().getCanonicalName());
	}

	public void commitChkpt(String fname) throws IOException {
		MP.printWarning(EC.GENERAL, "Checkpointing is not implemented for " + getClass().getCanonicalName());
	}

	public void recover(String fname) throws IOException {
		MP.printWarning(EC.GENERAL, "Checkpointing is not implemented for " + getClass().getCanonicalName());
	}
}
