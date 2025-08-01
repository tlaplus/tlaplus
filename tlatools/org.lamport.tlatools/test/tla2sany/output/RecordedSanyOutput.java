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

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

/**
 * A class recorded all SANY output as individual messages. Useful for
 * testing SANY's output behavior.
 */
public class RecordedSanyOutput implements SanyOutput {

  /**
   * A SANY output message. Can either be a single log message or the
   * contents of a {@link ByteArrayOutputStream} owned by some hopefully
   * short-lived section of code in SANY itself that writes to the stream.
   */
  public static class Message {
    private final LogLevel level;
    private final String format;
    private final Object[] args;
    private final ByteArrayOutputStream stream;

    public Message(LogLevel level, String format, Object... args) {
      this.level = level;
      this.format = format;
      this.args = args;
      this.stream = null;
    }

    public Message(LogLevel level, ByteArrayOutputStream stream) {
      this.level = level;
      this.format = null;
      this.args = null;
      this.stream = stream;
    }

    public LogLevel getLevel() {
      return this.level;
    }

    public String getText() {
      return
          (null == this.stream
          ? String.format(this.format, this.args)
          : this.stream.toString()) + '\n';
    }

    @Override
    public String toString() {
      return this.getText();
    }
  }

  private final List<Message> messages = new ArrayList<>();
  
  private final LogLevel logLevel;
  
  public RecordedSanyOutput(LogLevel logLevel) {
    this.logLevel = logLevel;
  }

  @Override
  public void log(LogLevel level, String format, Object... args) {
    if (level.ordinal() >= this.logLevel.ordinal()) {
      this.messages.add(new Message(level, format, args));
    }
  }

  @Override
  public PrintStream getStream(LogLevel level) {
    if (level.ordinal() >= this.logLevel.ordinal()) {
      ByteArrayOutputStream stream = new ByteArrayOutputStream();
      this.messages.add(new Message(level, stream));
      return new PrintStream(stream);
    } else {
      return SilentSanyOutput.NullOutputStream;
    }
  }

  public List<Message> getMessages() {
    return this.messages;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    for (Message msg : this.messages) {
      sb.append(msg.toString());
    }

    return sb.toString();
  }
}
