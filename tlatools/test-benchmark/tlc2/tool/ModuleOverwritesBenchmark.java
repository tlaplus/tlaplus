/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved.
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
package tlc2.tool;

import java.io.File;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.State;

import tlc2.tool.impl.FastTool;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.Value;
import util.SimpleFilenameToStream;
import util.ToolIO;
import util.UniqueString;

@State(Scope.Benchmark)
public class ModuleOverwritesBenchmark {

	/*
	 * Run with: java -jar target/benchmarks.jar -wi 2 -i 2 -f2 -rf json -rff
	 * ModuleOverwritesBenchmark-$(de +%s)-$(git rev-parse --short HEAD).json
	 * -jvmArgsPrepend "-Xms8192m -Xmx8192m" -jvmArgsAppend
	 * "-Dtlc2.tool.ModuleOverwritesBenchmark.base=/home/markus/src/TLA/tla/tlatools/test-model tlc2.tool.ModuleOverwritesBenchmark "
	 */
	
	private static final String BASE_PATH = System
			.getProperty(ModuleOverwritesBenchmark.class.getName() + ".base");

	private static final ITool tool;
	private static final TLCStateMut state;

	static {
		String dir = BASE_PATH + File.separator + "ModuleOverwrites";
		System.err.println(dir);
		ToolIO.setUserDir(dir);

		tool = new FastTool("", "ModuleOverwrites", "ModuleOverwrites", new SimpleFilenameToStream());

		state = (TLCStateMut) tool.getInitStates().elementAt(0);
	}

	@Benchmark
	public boolean aNoModuleOverwrite() {
		shuffleValues();
		return tool.isValid(tool.getInvariants()[0], state);
	}

	@Benchmark
	public boolean bModuleOverwrite() {
		shuffleValues();
		return tool.isValid(tool.getInvariants()[1], state);
	}

	@Benchmark
	public boolean cModuleOverwriteLinear() {
		shuffleValues();
		return tool.isValid(tool.getInvariants()[2], state);
	}

	private static final void shuffleValues() {
		final FcnRcdValue frv = (FcnRcdValue) state.getVals().get(UniqueString.uniqueStringOf("t"));

		final List<Value> values = Arrays.asList(frv.values);
		Collections.shuffle(values);

		for (int i = 0; i < values.size(); i++) {
			frv.values[i] = values.get(i);
		}
	}
}
