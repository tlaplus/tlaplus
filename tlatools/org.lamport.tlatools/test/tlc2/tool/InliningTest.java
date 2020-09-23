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
package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Test;

import jdk.jfr.Recording;
import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordedObject;
import jdk.jfr.consumer.RecordingFile;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.util.ExpectInlined;

@SuppressWarnings("restriction")
public class InliningTest extends ModelCheckerTestCase {

	/*
	 * The high-level idea is that we record the JVM's CompilerInlining while the
	 * JVM executes the test case. Afterwards, we check that a bunch of methods that
	 * are annotated with a marker have been correctly inlined.  For this to work,
	 * the test has to run long enough for the JVM to warm up.
	 * Thanks to https://twitter.com/ErikGahlin/status/1207018011674185728 for showing
	 * how to use the JFR API.
	 */
	
	private final Recording r = new Recording(); 

	public InliningTest() {
		super("InlineMC", "CodePlexBug08", ExitStatus.SUCCESS);
	}
	
	@Override
	protected void beforeSetUp() {
		r.enable("jdk.CompilerInlining"); 
		r.start(); 
	}
	
	// testSpec runs after model-checking.
	@Test
	public void testSpec() throws IOException {
		// ModelChecker has finished at this point.
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertZeroUncovered();
		
		// stop recording and read the jfr from from disk. Close the recording
		// afterwards.
		r.stop();
		Path p = Paths.get("test.jfr"); // test.jfr is the default file name.
		r.dump(p); 
		final List<RecordedEvent> recordedEvents = RecordingFile.readAllEvents(p);
		r.close();

		// "hot method too big" and not for "callee is too large":
		// https://www.lmax.com/blog/staff-blogs/2016/03/30/notes-hotspot-compiler-flags/
		final Set<RecordedObject> notInlined = recordedEvents.stream()
				.filter(ev -> ev.hasField("message"))
				.filter(ev -> "hot method too big".equals(ev.getString("message")))
				.map(ev -> (RecordedObject) ev.getValue("callee"))
				.filter(ro -> ro.getString("type").startsWith("tlc2/tool/impl/Tool")
						|| ro.getString("type").startsWith("tlc2/tool/impl/FastTool"))
				.collect(Collectors.toSet());
		
		// Make sure the test ran long enough for compilation to detect methods as hot.
		assertFalse(notInlined.isEmpty());
		
		// For now we only care that methods in Tool get correctly inlined
		// because its methods are guaranteed to be on the hot path.
		Method[] dm = Tool.class.getDeclaredMethods();
		for (int i = 0; i < dm.length; i++) {
			if (dm[i].getAnnotation(ExpectInlined.class) != null) {
				notIn(dm[i], notInlined);
			}
		}
		dm = FastTool.class.getDeclaredMethods();
		for (int i = 0; i < dm.length; i++) {
			if (dm[i].getAnnotation(ExpectInlined.class) != null) {
				notIn(dm[i], notInlined);
			}
		}
	}

	// This matching is likely brittle and will fail in ways that everybody will
	// agree should have been accounted for. When it does, please check if
	// RecordedObject has finally been changed to RecordedMethod
	// (https://twitter.com/ErikGahlin/status/1207536016858505217).
	private void notIn(final Method method, final Set<RecordedObject> notInlined) {
		final List<RecordedObject> methodNameMatches = notInlined.stream()
				.filter(ro -> method.getName().equals(ro.getString("name"))).collect(Collectors.toList());
		for (RecordedObject methodNameMatch : methodNameMatches) {
			assertTrue(isNoMatch(methodNameMatch, method));
		}
	}

	// I warned you that this doesn't work.
	private boolean isNoMatch(RecordedObject methodNameMatch, Method method) {
		final String desc = methodNameMatch.getString("descriptor");
		final String[] params = desc.substring(1, desc.indexOf(")")).split(";");
		if (method.getParameterCount() == params.length) {
			Class<?>[] parameters = method.getParameterTypes();
			for (int j = 0; j < params.length; j++) {
				final String paramType = parameters[j].toString().replace(".", "/").replaceFirst("^(class|interface) ",
						"L");
				if (!params[j].equals(paramType)) {
					return true;
				}
			}
			System.out.println(methodNameMatch);
			return false;
		}
		return true;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Override
	protected boolean doDump() {
		return false;
	}
}
