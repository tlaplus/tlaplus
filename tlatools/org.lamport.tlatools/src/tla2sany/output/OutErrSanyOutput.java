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
 * An output control class focusing on splitting output into two streams,
 * and ordinary output stream and an error stream. Also exposes ability to
 * silence all logs below a given {@link LogLevel}.
 */
public class OutErrSanyOutput implements SanyOutput {

  /**
   * The streams receiving output at various levels.
   */
  private final PrintStream[] outStreams = new PrintStream[LogLevel.values().length];

  /**
   * Initializes a new instance of the {@link OutErrSanyOutput} class with
   * the given parameters controlling what logs are output to where.
   *
   * @param out The stream to receive ordinary log output.
   * @param err The stream to receive erroneous log output.
   * @param outputLevel Only logs of at least this level are output.
   * @param errorLevel Logs of at least this level go to err; below, to out.
   */
  public OutErrSanyOutput(
      PrintStream out,
      PrintStream err,
      LogLevel outputLevel,
      LogLevel errorLevel
  ) {
    for (LogLevel level : LogLevel.values()) {
      this.outStreams[level.ordinal()] =
          level.ordinal() >= outputLevel.ordinal()
          ? level.ordinal() >= errorLevel.ordinal() ? err : out
          : SilentSanyOutput.NullOutputStream;
    }
  }

  @Override
  public void log(LogLevel level, String format, Object... args) {
    this.getStream(level).println(String.format(format, args));
  }

  @Override
  public PrintStream getStream(LogLevel level) {
    return this.outStreams[level.ordinal()];
  }
}
