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
package tla2sany.utilities;

import java.io.OutputStream;
import java.io.PrintStream;

/**
 * A class to centralize control of all SANY output. Should be used instead
 * of passing {@link PrintStream} instances around, referencing the static
 * fields of {@link util.ToolIO}, or referencing {@link System#in} or
 * {@link System#out} directly.
 */
public class SanyOutput {

  /**
   * Possible log levels. While this class has some conceptual overlap with
   * {@link tla2sany.semantic.ErrorCode.ErrorLevel}, these levels are focused
   * on controlling output shown to users. It is up to SANY front-end code to
   * route errors of varying levels to the appropriate log output level.
   */
  public enum LogLevel {

    /**
     * Used for extremely fine-grained logging that traces entry to & exit
     * from methods. Likely only useful to SANY developers.
     */
    TRACE,

    /**
     * Used for logs that can assist with bug diagnosis.
     */
    DEBUG,

    /**
     * Used to report ordinary progress & results.
     */
    INFO,

    /**
     * Used to alert users to occurrences which are likely undesired but not
     * fatal to the correct execution of the program.
     */
    WARNING,

    /**
     * Used to alert users to occurrences which are fatal to the correct
     * execution of the program.
     */
    ERROR
  }

  /**
   * The streams receiving output at various levels.
   */
  private final PrintStream[] outStreams = new PrintStream[LogLevel.values().length];

  private SanyOutput() { }

  /**
   * Initializes a new instance of the {@link SanyOutput} class with the
   * given parameters controlling what logs are output to where.
   *
   * @param out The stream to receive ordinary log output.
   * @param err The stream to receive erroneous log output.
   * @param outputLevel Only logs of at least this level are output.
   * @param errorLevel Logs of at least this level go to err; below, to out.
   */
  public SanyOutput(
      PrintStream out,
      PrintStream err,
      LogLevel outputLevel,
      LogLevel errorLevel
  ) {
    for (LogLevel level : LogLevel.values()) {
      this.outStreams[level.ordinal()] =
          level.ordinal() >= outputLevel.ordinal()
          ? level.ordinal() >= errorLevel.ordinal() ? err : out
          : new PrintStream(OutputStream.nullOutputStream());
    }
  }

  /**
   * Initializes a new instance of the {@link SanyOutput} class with all
   * output silenced. All output is send to {@link OutputStream#nullOutputStream()}.
   *
   * @return A new silenced instance of the {@link SanyOutput} class.
   */
  public static SanyOutput silent() {
    SanyOutput out = new SanyOutput();
    for (LogLevel level : LogLevel.values()) {
      out.outStreams[level.ordinal()] =
          new PrintStream(OutputStream.nullOutputStream());
    }

    return out;
  }

  /**
   * Logs a message by sending it to the output stream identified by the
   * given level. Uses println(), so appends a newline to the end of the
   * message. Interpolates the variable number of args into the given log
   * format string using {@link String#format}.
   *
   * @param level The level at which to log the message.
   * @param format A string into which args is interpolated.
   * @param args Parameters to interpolate into the format string.
   */
  public void log(LogLevel level, String format, Object... args) {
    this.getStream(level).println(String.format(format, args));
  }

  /**
   * Gets the stream associated with the given log level.
   *
   * @param level The level for which to retrieve the stream.
   * @return A stream associated with the given level.
   */
  public PrintStream getStream(LogLevel level) {
    return this.outStreams[level.ordinal()];
  }
}
