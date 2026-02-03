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
package tlc2.debug;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.lsp4j.debug.EvaluateArguments;
import org.eclipse.lsp4j.debug.EvaluateArgumentsContext;
import org.eclipse.lsp4j.debug.StackFrame;
import org.junit.Test;

import tlc2.output.EC;
import util.FilenameToStream;
import util.SimpleFilenameToStream;

public class Debug05SimTest extends TLCDebuggerTestCase {

	private static final String FOLDER = "debug";
	private static final String RM = "Debug05";

	public Debug05SimTest() {
		super(RM, FOLDER, new String[] { "-config", "Debug05.tla", "-simulate", "num=1", "-depth", "25" }, EC.ExitStatus.SUCCESS);
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Override
	protected FilenameToStream getResolver() {
		return new SimpleFilenameToStream(new String[] {BASE_DIR});
	}

	@Test
	public void testSpec() throws Exception {
		StackFrame[] stackFrames = debugger.stackTrace();
		
		EvaluateArguments ea = new EvaluateArguments();
		ea.setFrameId(stackFrames[0].getId());
		ea.setContext(EvaluateArgumentsContext.REPL);
		
		// Evaluate expressions that require Java module overrides.
		
		// An expression involving a module without any dependencies.
		ea.setExpression("LET N == INSTANCE Naturals IN N!+(1, 2)");
		assertEquals("3", debugger.evaluate(ea).get().getResult());
		
		// An expression involving a module with one dependency.
		ea.setExpression("LET S == INSTANCE Sequences IN S!Len(<<1,2,3>>)");
		assertEquals("3", debugger.evaluate(ea).get().getResult());

		ea.setExpression("LET N == INSTANCE Integers IN N!+(1, 2)");
		assertEquals("3", debugger.evaluate(ea).get().getResult());
		
		// An expression involving a module with multiple dependencies.
		ea.setExpression("LET T == INSTANCE TLC IN T!RandomElement({1})");
		assertEquals("1", debugger.evaluate(ea).get().getResult());
		
		ea.setExpression("LET B == INSTANCE Bags IN B!SetToBag({\"a\", \"a\", \"b\"})");
		String result = debugger.evaluate(ea).get().getResult();
		assertTrue(result.equals("[b |-> 1, a |-> 1]") || result.equals("[a |-> 1, b |-> 1]"));
		
		ea.setExpression("LET J == INSTANCE Json IN J!ToJson({1,2,3})");
		assertEquals("[1,2,3]", debugger.evaluate(ea).get().getResult());
		
		// 88888888888888888888888888888888888888888888888888888 //

		debugger.setSpecBreakpoint();
		debugger.continue_();

		for (int i = 1; i < 20; i++) {
			stackFrames = debugger.continue_();
			StackFrame stackFrame = stackFrames[0];
			ea.setFrameId(stackFrame.getId());

			String traceFile = "Debug05SimTest.json";
			ea.setExpression("LET J == INSTANCE _JsonTrace WITH _JsonTraceFile <- \"" + traceFile
					+ "\", _JsonTraceInputFile <- \"" + traceFile + "\" IN J!_JsonTrace");
			assertEquals("TRUE", debugger.evaluate(ea).get().getResult());

			// Validate the content of the generated file (by using the very functionality
			// we are testing).
			ea.setExpression("LET S == INSTANCE Sequences J == INSTANCE Json T == J!JsonDeserialize(\"" + traceFile
					+ "\") IN S!Len(T.counterexample.state) = " + i);
			assertEquals("TRUE", debugger.evaluate(ea).get().getResult());

			// 88888888888888888888888888888888888888888888888888888 //
			
			traceFile = "Debug05SimTest.bin";
			ea.setExpression("LET J == INSTANCE _TLCTrace WITH _TLCTraceFile <- \"" + traceFile
					+ "\", _TLCTraceInputFile <- \"" + traceFile + "\" IN J!_TLCTrace");
			assertEquals("TRUE", debugger.evaluate(ea).get().getResult());

			// 88888888888888888888888888888888888888888888888888888 //
		}
		
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}