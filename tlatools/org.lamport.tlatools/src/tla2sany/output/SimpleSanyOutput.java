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
 * An output control class that routes all output above a given level to a
 * single provided {@link PrintStream} instance.
 */
public class SimpleSanyOutput implements SanyOutput {

  /**
   * The stream receiving non-silenced output.
   */
  private final PrintStream out;

  /**
   * Output below this level is silenced.
   */
  private final LogLevel logLevel;

  /**
   * Initializes a new instance of the {@link SimpleSanyOutput} class which
   * routes all output of sufficient level to the given {@link PrintStream}
   * instance.
   *
   * @param out The stream receiving non-silenced output.
   * @param logLevel Output below this level is silenced.
   */
  public SimpleSanyOutput(PrintStream out, LogLevel logLevel) {
    if (null == out) {
      throw new IllegalArgumentException("out stream cannot be null");
    }

    this.out = out;
    this.logLevel = logLevel;
  }

  @Override
  public void log(LogLevel level, String format, Object... args) {
    this.getStream(level).println(String.format(format, args));
  }

  @Override
  public PrintStream getStream(LogLevel level) {
    return
        level.ordinal() >= this.logLevel.ordinal()
        ? this.out : SilentSanyOutput.NullOutputStream;
  }
}
