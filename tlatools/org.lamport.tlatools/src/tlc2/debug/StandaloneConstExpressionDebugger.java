/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
package tlc2.debug;

import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;

import org.eclipse.lsp4j.debug.OutputEventArguments;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.TLCGlobals;
import tlc2.tool.impl.DebugTool;
import tlc2.tool.impl.Tool;
import tlc2.util.FP64;
import util.SimpleFilenameToStream;
import util.ToolIO;

/*
 * This debugger waits for a front-end to connect with a path to a spec.  This spec has to define a "debugMe" const-level operator that this debugger will evaluate and debug 
 */
public class StandaloneConstExpressionDebugger extends TLCDebugger {

	// THIS SCED HASN'T BEEN UPDATED TO REFLECT WHAT IS GOING ON IN TLCDEBUGGER AND,
	// THUS, PROBABLY DOESN'T WORK ANYMORE!!!
	
	public static void main(String[] args) throws IOException, InterruptedException, ExecutionException {
		new StandaloneConstExpressionDebugger();
	}

	public StandaloneConstExpressionDebugger() {
		super();
	}

	@Override
	public CompletableFuture<Void> launch(Map<String, Object> args) {
		LOGGER.finer("launch");

		final Path p = Paths.get((String) args.get("program"));
		final String specPath = p.getParent().toAbsolutePath().toString();
		final String specName = p.getFileName().toFile().toString();
		final String moduleName = specName.replaceFirst(".tla$", "");

		// IValue#hashCode calls below require fingerprints to be correctly initialized.
		// TODO: Investigate if this is still needed since Variable and its related
		// classes were changed to not trigger Value#hashCode as a side-effect.
		FP64.Init();

		// Listen to that SANY and TLC have to say, and what gets written with TLC!Print*.
		ToolIO.out = new PrintStream(ToolIO.out) {
			// See tlc2.debug.AttachingDebugger.AttachingDebugger(...).new PrintStream() {...}
			@Override
			public void println(String str) {
				((PrintStream) out).println(str);
				sendOutput(str + "\n");
			}

			@Override
			public void print(String str) {
				((PrintStream) out).print(str);
				sendOutput(str);
			}

			private void sendOutput(String str) {
				final OutputEventArguments oea = new OutputEventArguments();
				oea.setOutput(str);
				if (launcher != null) {
					launcher.getRemoteProxy().output(oea);
				}
			}
		};
		ToolIO.reset();
		
		final Tool tool = new DebugTool(moduleName, specName, new SimpleFilenameToStream(specPath), new HashMap<>(), this);
		final ModuleNode module = tool.getSpecProcessor().getRootModule();
		// The spec has to have an "debugMe" operator.
		final OpDefNode valueNode = module.getOpDef("debugMe");

		// Kick off the evaluation of the expression in Tool in a different thread.
		Executors.newSingleThreadExecutor().submit(() -> {
			// Expanding values causes them to be un-lazied/enumerated, which we don't want
			// as a side-effect of the debugger.
			TLCGlobals.expand = false;
			
			tool.eval(valueNode.getBody());
		});

		return CompletableFuture.completedFuture(null);
	}
}
