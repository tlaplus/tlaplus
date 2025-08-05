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
package util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import static org.junit.Assert.assertArrayEquals;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.Test;

/**
 * Tests for the {@link NamedInputStream} class
 */
public class NamedInputStreamTest {

  @Test
  public void apiTest() throws IOException {
    Path inputFile = Files.createTempFile("NISTest", ".tla");
    String fileName = inputFile.getFileName().toString();
    String moduleName = fileName.substring(0, fileName.length() - 4);
    byte[] contents = String.format("---- MODULE %s ----\nASSUME TRUE\n====", moduleName).getBytes();
    Files.write(inputFile, contents);
    NamedInputStream nis = new NamedInputStream(fileName, moduleName, inputFile.toFile());
    assertEquals(fileName, nis.getName());
    assertEquals(fileName, nis.getFileName());
    assertEquals(moduleName, nis.getModuleName());
    assertEquals(inputFile.toFile(), nis.sourceFile());
    assertEquals(inputFile.toRealPath(), nis.getAbsoluteResolvedPath());
    assertEquals(String.format("[ fileName: %s, moduleName: %s ]", fileName, moduleName), nis.toString());
    assertEquals(1, NamedInputStream.getNumberOfreferences());
    assertArrayEquals(contents, nis.readAllBytes());
    nis.close();
    assertEquals(0, NamedInputStream.getNumberOfreferences());
  }

  @Test
  public void referenceCountingTest() throws IOException {
    Path inputFile = Files.createTempFile("NISTest", ".tla");
    String fileName = inputFile.getFileName().toString();
    String moduleName = fileName.substring(0, fileName.length() - 4);
    byte[] contents = String.format("---- MODULE %s ----\nASSUME TRUE\n====", moduleName).getBytes();
    Files.write(inputFile, contents);

    assertEquals(0, NamedInputStream.getNumberOfreferences());
    NamedInputStream nis1 = new NamedInputStream(fileName, moduleName, inputFile.toFile());
    assertEquals(1, NamedInputStream.getNumberOfreferences());
    NamedInputStream nis2 = new NamedInputStream(fileName, moduleName, inputFile.toFile());
    assertEquals(2, NamedInputStream.getNumberOfreferences());
    NamedInputStream nis3 = new NamedInputStream(fileName, moduleName, inputFile.toFile());
    assertEquals(3, NamedInputStream.getNumberOfreferences());
    nis1.close();
    assertEquals(2, NamedInputStream.getNumberOfreferences());
    nis3.close();
    assertEquals(1, NamedInputStream.getNumberOfreferences());
    nis2.close();
    assertEquals(0, NamedInputStream.getNumberOfreferences());
  }

  @Test
  public void invalidFileTest() {
    try (NamedInputStream nis = new NamedInputStream("ModuleName.tla", "ModuleName", null)) {
      fail("Expected NullPointerException");
    } catch (NullPointerException e) {
      // Expected
    } catch (FileNotFoundException e) {
      fail("Expected NullPointerException");
    } catch (IOException e) {
      fail("Expected NullPointerException");
    }

    try (NamedInputStream nis = new NamedInputStream("ModuleName.tla", "ModuleName", new File("this/path/does/not/exist/12345/ModuleName.tla"))) {
      fail("Expected FileNotFoundException");
    } catch (NullPointerException e) {
      fail("Expected FileNotFoundException");
    } catch (FileNotFoundException e) {
      // Expected
    } catch (IOException e) {
      fail("Expected FileNotFoundException");
    }
  }
}
