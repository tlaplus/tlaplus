/*******************************************************************************
 * Copyright (c) 2024 Linux Foundation. All rights reserved.
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

import org.junit.Assert;
import org.junit.Test;

import tla2sany.st.Location;

/**
 * Tests for the {@link Errors} class, to ensure its workings remain
 * unchanged as it is refactored internally.
 */
public class TestErrors {

  private static int seed = 0;

  private static Location genLocation() {
    final String filename = String.format("Test%d.tla", seed);
    final Location loc = new Location(filename, seed*3, seed*5, seed*7, seed*11);
    seed++;
    return loc;
  }

  @Test
  public void testWarningMessages() {
    final Errors log = new Errors();

    final Location loc1 = genLocation();
    final String message1 = "This is a test warning message";
    log.addWarning(loc1, message1);
    final String expected1 = loc1.toString() + "\n\n" + message1;

    final Location loc2 = genLocation();
    final String message2 = "This is another test warning message";
    log.addWarning(loc2, message2);
    final String expected2 = loc2.toString() + "\n\n" + message2;

    final Location loc3 = Location.nullLoc;
    final String message3 = "This is yet another test warning message";
    log.addWarning(null, message3);
    final String expected3 = loc3.toString() + "\n\n" + message3;

    final String[] expected = new String[] { expected1, expected2, expected3 };
    final String[] actual = log.getWarnings();
    Assert.assertArrayEquals(expected, actual);
    Assert.assertFalse(log.isFailure());
    Assert.assertTrue(log.isSuccess());
    Assert.assertEquals(expected.length, log.getNumMessages());
    Assert.assertEquals(0, log.getNumErrors());
    Assert.assertEquals(0, log.getNumAbortsAndErrors());
    Assert.assertEquals(0, log.getErrors().length);
    Assert.assertEquals(0, log.getAborts().length);

    final String actualSummary = log.toString();
    for (final String expectedMessage : expected) {
      Assert.assertTrue(actualSummary.contains(expectedMessage));
    }
  }

  @Test
  public void testErrorMessages() {
    final Errors log = new Errors();

    final Location loc1 = genLocation();
    final String message1 = "This is a test error message";
    log.addError(loc1, message1);
    final String expected1 = loc1.toString() + "\n\n" + message1;

    final Location loc2 = genLocation();
    final String message2 = "This is another test error message";
    log.addError(loc2, message2);
    final String expected2 = loc2.toString() + "\n\n" + message2;

    final Location loc3 = Location.nullLoc;
    final String message3 = "This is yet another test error message";
    log.addError(null, message3);
    final String expected3 = loc3.toString() + "\n\n" + message3;

    final String[] expected = new String[] { expected1, expected2, expected3 };
    final String[] actual = log.getErrors();
    Assert.assertArrayEquals(expected, actual);
    Assert.assertTrue(log.isFailure());
    Assert.assertFalse(log.isSuccess());
    Assert.assertEquals(expected.length, log.getNumMessages());
    Assert.assertEquals(expected.length, log.getNumErrors());
    Assert.assertEquals(expected.length, log.getNumAbortsAndErrors());
    Assert.assertEquals(0, log.getWarnings().length);
    Assert.assertEquals(0, log.getAborts().length);

    final String actualSummary = log.toString();
    for (final String expectedMessage : expected) {
      Assert.assertTrue(actualSummary.contains(expectedMessage));
    }
  }

  @Test
  public void testAbortMessages() {
    final Errors log = new Errors();

    final Location loc1 = genLocation();
    final String message1 = "This is a test abort message";
    try {
      log.addAbort(loc1, message1);
      Assert.fail();
    } catch (AbortException e) { }
    final String expected1 = loc1.toString() + "\n\n" + message1;

    final Location loc2 = genLocation();
    final String message2 = "This is another test abort message";
    try {
      log.addAbort(loc2, message2);
      Assert.fail();
    } catch (AbortException e) { }
    final String expected2 = loc2.toString() + "\n\n" + message2;

    final Location loc3 = Location.nullLoc;
    final String message3 = "This is yet another test abort message";
    try {
      log.addAbort(null, message3);
      Assert.fail();
    } catch (AbortException e) { }
    final String expected3 = loc3.toString() + "\n\n" + message3;

    final String[] expected = new String[] { expected1, expected2, expected3 };
    final String[] actual = log.getAborts();
    Assert.assertArrayEquals(expected, actual);
    Assert.assertTrue(log.isFailure());
    Assert.assertFalse(log.isSuccess());
    Assert.assertEquals(expected.length, log.getNumMessages());
    Assert.assertEquals(0, log.getNumErrors());
    Assert.assertEquals(expected.length, log.getNumAbortsAndErrors());
    Assert.assertEquals(0, log.getWarnings().length);
    Assert.assertEquals(expected.length, log.getAborts().length);

    final String actualSummary = log.toString();
    for (final String expectedMessage : expected) {
      Assert.assertTrue(actualSummary.contains(expectedMessage));
    }
  }

  @Test
  public void testAlternativeAbortFunctions() {
    final Errors log = new Errors();

    final Location loc1 = genLocation();
    final String message1 = "This is a test abort message";
    try {
      log.addAbort(loc1, message1, false);
    } catch (AbortException e) {
      Assert.fail();
    }
    final String expected1 = loc1.toString() + "\n\n" + message1;

    final Location loc2 = Location.nullLoc;
    final String message2 = "This is another test abort message";
    try {
      log.addAbort(message2, false);
    } catch (AbortException e) {
      Assert.fail();
    }
    final String expected2 = loc2.toString() + "\n\n" + message2;

    final Location loc3 = Location.nullLoc;
    final String message3 = "This is yet another test abort message";
    try {
      log.addAbort(message3);
      Assert.fail();
    } catch (AbortException e) { }
    final String expected3 = loc3.toString() + "\n\n" + message3;

    final String[] expected = new String[] { expected1, expected2, expected3 };
    final String[] actual = log.getAborts();
    Assert.assertArrayEquals(expected, actual);
    Assert.assertTrue(log.isFailure());
    Assert.assertFalse(log.isSuccess());
    Assert.assertEquals(expected.length, log.getNumMessages());
    Assert.assertEquals(0, log.getNumErrors());
    Assert.assertEquals(expected.length, log.getNumAbortsAndErrors());
    Assert.assertEquals(0, log.getWarnings().length);
    Assert.assertEquals(expected.length, log.getAborts().length);

    final String actualSummary = log.toString();
    for (final String expectedMessage : expected) {
      Assert.assertTrue(actualSummary.contains(expectedMessage));
    }
  }

  @Test
  public void testMixedMessageLevels() {
    final Errors log = new Errors();

    final Location loc1 = genLocation();
    final String message1 = "This is a test warning message";
    log.addWarning(loc1, message1);
    final String expectedWarning = loc1.toString() + "\n\n" + message1;
    final String[] expectedWarnings = new String[] { expectedWarning };

    final Location loc2 = genLocation();
    final String message2 = "This is a test error message";
    log.addError(loc2, message2);
    final String expectedError = loc2.toString() + "\n\n" + message2;
    final String[] expectedErrors = new String[] { expectedError };

    final Location loc3 = genLocation();
    final String message3 = "This is a test abort message";
    try {
      log.addAbort(loc3, message3);
      Assert.fail();
    } catch (AbortException e) { }
    final String expectedAbort = loc3.toString() + "\n\n" + message3;
    final String[] expectedAborts = new String[] { expectedAbort };

    Assert.assertArrayEquals(expectedWarnings, log.getWarnings());
    Assert.assertArrayEquals(expectedErrors, log.getErrors());
    Assert.assertArrayEquals(expectedAborts, log.getAborts());
    Assert.assertTrue(log.isFailure());
    Assert.assertFalse(log.isSuccess());
    Assert.assertEquals(expectedWarnings.length + expectedErrors.length + expectedAborts.length, log.getNumMessages());
    Assert.assertEquals(expectedErrors.length, log.getNumErrors());
    Assert.assertEquals(expectedErrors.length + expectedAborts.length, log.getNumAbortsAndErrors());

    final String actualSummary = log.toString();
    Assert.assertTrue(actualSummary.contains(expectedWarning));
    Assert.assertTrue(actualSummary.contains(expectedError));
    Assert.assertTrue(actualSummary.contains(expectedAbort));
  }

  @Test
  public void testDuplicateErrorsIgnored() {
    final Errors log = new Errors();

    final Location loc1 = genLocation();
    final String message1 = "This is a test warning message";
    log.addWarning(loc1, message1);
    log.addWarning(loc1, message1);
    log.addWarning(loc1, message1);
    final String expectedWarning = loc1.toString() + "\n\n" + message1;
    final String[] expectedWarnings = new String[] { expectedWarning };

    final Location loc2 = genLocation();
    final String message2 = "This is a test error message";
    log.addError(loc2, message2);
    log.addError(loc2, message2);
    log.addError(loc2, message2);
    final String expectedError = loc2.toString() + "\n\n" + message2;
    final String[] expectedErrors = new String[] { expectedError };

    final Location loc3 = genLocation();
    final String message3 = "This is a test abort message";
    try {
      log.addAbort(loc3, message3, false);
      log.addAbort(loc3, message3, false);
      log.addAbort(loc3, message3, false);
    } catch (AbortException e) {
      Assert.fail();
    }
    final String expectedAbort = loc3.toString() + "\n\n" + message3;
    final String[] expectedAborts = new String[] { expectedAbort };

    Assert.assertArrayEquals(expectedWarnings, log.getWarnings());
    Assert.assertArrayEquals(expectedErrors, log.getErrors());
    Assert.assertArrayEquals(expectedAborts, log.getAborts());
    Assert.assertTrue(log.isFailure());
    Assert.assertFalse(log.isSuccess());
    Assert.assertEquals(expectedWarnings.length + expectedErrors.length + expectedAborts.length, log.getNumMessages());
    Assert.assertEquals(expectedErrors.length, log.getNumErrors());
    Assert.assertEquals(expectedErrors.length + expectedAborts.length, log.getNumAbortsAndErrors());

    final String actualSummary = log.toString();
    Assert.assertTrue(actualSummary.contains(expectedWarning));
    Assert.assertTrue(actualSummary.contains(expectedError));
    Assert.assertTrue(actualSummary.contains(expectedAbort));
  }
}
