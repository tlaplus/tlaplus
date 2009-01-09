// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:27:29 PST by lamport
//      modified on Wed Jan 10 00:11:43 PST 2001 by yuanyu

package tlc2.tool;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

public class FileClassLoader extends ClassLoader {
  /* Load a class from a file. */
  private String dir;

  public FileClassLoader(String dir) {
    this.dir = dir;
    if (dir.length() != 0 &&
	!dir.endsWith(File.separator)) {
      this.dir += File.separator;
    }
  }
    
  private byte[] loadClassData(String name) {
    byte[] bytes = null;
    String fileName = name + ".class";
    try {
      FileInputStream fis = new FileInputStream(this.dir + fileName);
      int size = fis.available();
      bytes = new byte[size];
      fis.read(bytes);
      fis.close();
    }
    catch (IOException e) { bytes = null; }
    return bytes;
  }

  public synchronized Class loadClass(String name, boolean resolve) {
    Class c = null;
    byte[] data = loadClassData(name);
    if (data != null) {
      c = defineClass(name, data, 0, data.length);
      if (resolve) resolveClass(c);
    }
    return c;
  }

  public static void main(String argv[]) {
    FileClassLoader fcl = new FileClassLoader("/udir/yuanyu/proj/tlc/module");
    try {
      Class c = fcl.loadClass("Strings", true);  // must set CLASSPATH correctly
      System.err.println(c);
    }
    catch (Exception e) {
      // Assert.printStack();
      System.err.println("Error: " + e.getMessage());
    }
  }

}


