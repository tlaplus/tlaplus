/*******************************************************************************
 * Copyright (c) 2003 Compaq Corporation. All rights reserved.
 * Copyright (c) 2003 Microsoft Corporation. All rights reserved.
 * Copyright (c) 2025 Linux Foundation. All rights reserved.
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
package tla2sany.semantic;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import tla2sany.semantic.ErrorCode.ErrorLevel;
import tla2sany.st.Location;

/**
 * SANY's central logging class. Messages are tagged with a standardized
 * {@link ErrorCode} and stored for later display or processing.
 */
public class Errors {

  /**
   * Un-serialized information about an error.
   */
  public static final class ErrorDetails {

    private final ErrorCode code;

    private final Location location;

    private final String format;

    private final Object[] parameters;

    ErrorDetails(ErrorCode code, Location location, String format, Object... parameters) {
      this.code = code;
      this.location = location;
      this.format = format;
      this.parameters = parameters;
    }

    public ErrorCode getCode() {
      return this.code;
    }

    public Location getLocation() {
      return this.location;
    }

    public String getMessage() {
      return String.format(this.format, this.parameters);
    }

    public List<Object> getParameters() {
      return List.of(this.parameters);
    }

    @Override
    public String toString() {
      return this.location.toString() + "\n\n" + this.getMessage();
    }

    @Override
    public boolean equals(Object o) {
      if (!(o instanceof ErrorDetails)) {
        return false;
      }
      final ErrorDetails other = (ErrorDetails)o;
      return this.code.equals(other.code)
          && this.location.equals(other.location)
          && this.format.equals(other.format)
          && Arrays.equals(this.parameters, other.parameters);
    }
  }

  /**
   * A centralized list of recorded messages.
   */
  private final List<ErrorDetails> messages = new ArrayList<ErrorDetails>();

  /**
   * Retrieves all recorded messages of exactly the given level.
   *
   * @param level The level of messages to retrieve.
   * @return All recorded messages of exactly the given level.
   */
  public List<ErrorDetails> getMessagesOfLevel(ErrorLevel level) {
    return this.messages.stream().filter(
        msg -> msg.getCode().getSeverityLevel().equals(level)
      ).collect(Collectors.toList());
  }

  /**
   * Retrieves all recorded messages.
   *
   * @return A list of all recorded messages.
   */
  public List<ErrorDetails> getMessages() {
    return new ArrayList<ErrorDetails>(this.messages);
  }

  public List<ErrorDetails> getErrorDetails() {
    return this.getMessagesOfLevel(ErrorLevel.ERROR);
  }

  public String[] getErrors() {
    return this.getErrorDetails().stream()
        .map(ErrorDetails::toString).toArray(String[]::new);
  }

  public List<ErrorDetails> getWarningDetails() {
    return this.getMessagesOfLevel(ErrorLevel.WARNING);
  }

  public String[] getWarnings() {
    return this.getWarningDetails().stream()
        .map(ErrorDetails::toString).toArray(String[]::new);
  }

  /**
   * Append a message to the log. If location is null, the value
   * {@link Location.nullLoc} is assigned. Idempotent; will not append the
   * same message to the log multiple times. Returns {@link AbortException}
   * which can optionally be thrown by the caller, if error is fatal.
   *
   * @param code The standardized error code associated with the message.
   * @param loc A spec location associated with the message.
   * @param format A message into which parameters are interpolated.
   * @param parameters A list of standardized values attached to the error.
   * @return An exception which can optionally be thrown by the caller.
   */
  public final AbortException addMessage(ErrorCode code, Location loc, String format, Object... parameters) {
    loc = null == loc ? Location.nullLoc : loc;
    final ErrorDetails message = new ErrorDetails(code, loc, format, parameters);
    if (!this.messages.contains(message)) {
      this.messages.add(message);
    }

    return new AbortException(message, this);
  }

  /**
   * Use {@link Errors#addMessage(ErrorCode, Location, String) } method instead.
   */
  @Deprecated
  public final void addWarning(ErrorCode code, Location loc, String str) {
    this.addMessage(code, loc, str);
  }

  /**
   * Use {@link Errors#addMessage(ErrorCode, Location, String) } method instead.
   */
  @Deprecated
  public final AbortException addError(ErrorCode code, Location loc, String str) {
    return this.addMessage(code, loc, str);
  }

  public final boolean isSuccess() {
    return this.getErrorDetails().isEmpty();
  }

  public final boolean isFailure() {
    return !this.isSuccess();
  }

  public final int getNumErrors() {
    return this.getErrorDetails().size();
  }

  public final int getNumMessages() {
    return this.messages.size();
  }

  public final String toString()  {
    StringBuffer ret = new StringBuffer("");

    final List<ErrorDetails> errors = this.getErrorDetails();
    ret.append((errors.size() > 0) ? "*** Errors: " + errors.size() + "\n\n" : "");
    for (final ErrorDetails error : errors) {
      ret.append(error.toString() + "\n\n\n");
    }

    final List<ErrorDetails> warnings = this.getWarningDetails();
    ret.append((warnings.size() > 0) ? "*** Warnings: " + warnings.size() + "\n\n" : "");
    for (final ErrorDetails error : warnings) {
      ret.append(error.toString() + "\n\n\n");
    }

    return ret.toString();
  }
}
