/*******************************************************************************
 * Copyright (c) 2025 The Linux Foundation. All rights reserved.
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
 ******************************************************************************/
package tla2sany.output;

import java.io.PrintStream;

/**
 * An interface to centralize control of all SANY output. Should be used
 * instead of passing {@link PrintStream} instances around, referencing the
 * static fields of {@link util.ToolIO}, or referencing {@link System#in} or
 * {@link System#out} directly.
 */
public interface SanyOutput {

  /**
   * Logs a message at the given {@link LogLevel}. If applicable, a newline
   * is appended to the given log message to separate it from subsequent
   * messages, similar to {@link PrintStream#println()}. The variable args
   * are interpolated into the format string using {@link String#format}.
   *
   * @param level The level at which to log the message.
   * @param format A string into which args is interpolated.
   * @param args Parameters to interpolate into the format string.
   */
  public void log(LogLevel level, String format, Object... args);

  /**
   * For the rare cases requiring an explicit stream associated with the
   * given {@link LogLevel}, for example {@link Exception#printStackTrace(PrintStream)},
   * retrieve a stream to which output can be printed. Callers must not close
   * the returned {@link PrintStream} instance.
   *
   * @param level The level associated with the stream.
   * @return A {@link PrintStream} associated with the given level.
   */
  public PrintStream getStream(LogLevel level);
}
