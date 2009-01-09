// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

public class FileUtil {

  /**
   * deletes the file or directory. Returns true iff the deletion
   * succeeds. The argument recurse forces the deletion of non-empty
   * directory.
   */
  public static boolean deleteDir(File file, boolean recurse) {
    if (file.exists()) {
      if (file.isFile() || !recurse) {
	return file.delete();
      }
      // must be a directory:
      String[] fnames = file.list();
      for (int i = 0; i < fnames.length; i++) {
	if (!deleteDir(new File(file, fnames[i]), recurse)) {
	  return false;
	}
      }
      return file.delete();
    }
    return true;
  }

  public static InputStream newBZFileInputStream(String file, 
						 boolean useGzip, 
						 boolean useIBuffers,
						 int buffersize)
  throws IOException, FileNotFoundException {
    if (useGzip) {
      return new GZIPInputStream(new FileInputStream(file), buffersize);
    }
    else if (useIBuffers) {
      return new BufferedInputStream (new FileInputStream(file), buffersize);
    }
    else {
      return new FileInputStream(file);
    }
  }

  public static OutputStream newBZFileOutputStream(String file,
						   boolean useGzip, 
						   boolean useOBuffers,
						   int buffersize)
  throws IOException {
    if (useGzip) {
      return new GZIPOutputStream(new FileOutputStream(file), buffersize);
    }
    else if (useOBuffers) {
      return new BufferedOutputStream (new FileOutputStream(file), buffersize);
    }
    else {
      return new FileOutputStream(file);
    }
  }

  public static OutputStream newBZFileOutputStream(String file,
						   boolean useGzip, 
						   boolean useOBuffers,
						   int buffersize, boolean app)
  throws IOException {
    if (useGzip) {
      return new GZIPOutputStream(new FileOutputStream(file, app), buffersize);
    }
    else if (useOBuffers) {
      return new BufferedOutputStream (new FileOutputStream(file, app), buffersize);
    }
    else {
      return new FileOutputStream(file, app);
    }
  }

  public static void printArrayOfBigInts(InputStream in) throws IOException {
    BigInt[] A = ByteUtils.readSizeArrayOfSizeBigInts(in);
    for (int i = 0; i < A.length; i++) {
      System.out.println(A[i]);
    }
  }
  
}
