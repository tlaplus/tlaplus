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
package util;

// Label is only used by Mission control but not relevant for the recording itself.
public class TLAFlightRecorder {
	
    @jdk.jfr.Label("Progress")
    @jdk.jfr.Category({"TLC", "Progress"})
    @jdk.jfr.StackTrace(false)// No need to capture the stack of the reporting (main) thread when it emits the event.
	private static class ProgressEvent extends jdk.jfr.Event {
		@jdk.jfr.Label("States generated per minute")
		@jdk.jfr.Unsigned
		private long spm;
		@jdk.jfr.Label("Distinct states generated per minute")
		@jdk.jfr.Unsigned
		private long dspm;
		@jdk.jfr.Label("Unseen States")
		@jdk.jfr.Unsigned
		private long unseen;
		@jdk.jfr.Label("Diameter")
		@jdk.jfr.Unsigned
		private int diameter;
		@jdk.jfr.Label("States Generated")
		@jdk.jfr.Unsigned
		private long states;
		@jdk.jfr.Label("Distinct States Generated")
		@jdk.jfr.Unsigned
		private long distStates;
		@jdk.jfr.Label("Model Checking done")
		private boolean isFinal;
	}

	public static void progress(boolean isFinal, final int diameter, final long states, final long distinctStates, final long unseen,
			final long statesPerMinute, final long distinctStatesPerMinute) {
		try {
			final ProgressEvent e = new ProgressEvent();
			e.isFinal = isFinal;
			e.spm = statesPerMinute;
			e.dspm = distinctStatesPerMinute;
			e.diameter = diameter;
			e.unseen = unseen;
			e.states = states;
			e.distStates = distinctStates;
			e.commit();
		} catch (NoClassDefFoundError e) {
			// Java 1.8 doesn't have jdk.jfr.Event and thus this flight recording is broken.
		}
	}
	
    @jdk.jfr.Label("Message")
    @jdk.jfr.Category({"TLC"})
    @jdk.jfr.StackTrace(false)// No need to capture the stack of the reporting (main) thread when it emits the event.
	private static class MessageEvent extends jdk.jfr.Event {
		@jdk.jfr.Label("Message")
		public String message;
    }

	public static String message(final String message) {
		try {
			final MessageEvent e = new MessageEvent();
			e.message = message;
			e.commit();
		} catch (NoClassDefFoundError e) {
			// Java 1.8 doesn't have jdk.jfr.Event and thus this flight recording is broken.
		}
		return message;
	}
}