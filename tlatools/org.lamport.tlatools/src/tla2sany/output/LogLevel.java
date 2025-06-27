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
