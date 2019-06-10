/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package org.lamport.tla.toolbox.tool.tlc.output.data;

import static org.junit.Assert.*;

import org.junit.Test;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.FPSetConfiguration;

public class TLCModelLaunchDataProviderTest {
	
	@Test
	public void testDFSSingleWorker() {
		TLCGlobals.setNumWorkers(1);
		String startupMessage = MP.getMessage(MP.NONE, EC.TLC_MODE_MC_DFS,
				TLC.getModelCheckingRuntime(23, new FPSetConfiguration()).values().toArray(new String[0]));		
		
		assertEquals(23, TLCModelLaunchDataProvider.getFPIndex(startupMessage));
	}
	
	@Test
	public void testDFSMultipleWorkers() {
		TLCGlobals.setNumWorkers(3);
		String startupMessage = MP.getMessage(MP.NONE, EC.TLC_MODE_MC_DFS,
				TLC.getModelCheckingRuntime(4, new FPSetConfiguration()).values().toArray(new String[0]));		
		
		assertEquals(4, TLCModelLaunchDataProvider.getFPIndex(startupMessage));
	}

	@Test
	public void testBFSSingleWorker() {
		TLCGlobals.setNumWorkers(1);
		String startupMessage = MP.getMessage(MP.NONE, EC.TLC_MODE_MC,
				TLC.getModelCheckingRuntime(4711, new FPSetConfiguration()).values().toArray(new String[0]));		
		
		assertEquals(4711, TLCModelLaunchDataProvider.getFPIndex(startupMessage));
	}

	@Test
	public void testBFSMultipleWorkers() {
		TLCGlobals.setNumWorkers(2);
		String startupMessage = MP.getMessage(MP.NONE, EC.TLC_MODE_MC,
				TLC.getModelCheckingRuntime(42, new FPSetConfiguration()).values().toArray(new String[0]));		
		
		assertEquals(42, TLCModelLaunchDataProvider.getFPIndex(startupMessage));
	}
}
