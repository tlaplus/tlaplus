/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved. 
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
package tlc2.value.impl;

import java.util.ArrayList;
import java.util.List;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.listener.PreciseRaceDetector;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.bytecode.FieldInstruction;

/**
 * A {@link PreciseRaceDetector} that does not report accesses to volatile
 * fields, which are synchronization actions and thus never a data race in the
 * Java memory model.
 */
public class DataRaceDetector extends PreciseRaceDetector {

	public DataRaceDetector(final Config conf) {
		super(conf);
	}

	@Override
	protected boolean checkRace(final ThreadInfo[] threads) {
		final List<ThreadInfo> plain = new ArrayList<>(threads.length);
		for (final ThreadInfo ti : threads) {
			final Instruction pc = ti.getPC();
			if (pc instanceof FieldInstruction && ((FieldInstruction) pc).getFieldInfo().isVolatile()) {
				continue;
			}
			plain.add(ti);
		}
		return super.checkRace(plain.toArray(new ThreadInfo[plain.size()]));
	}
}
