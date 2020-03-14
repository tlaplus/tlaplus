// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.Enumeration;

import util.FileUtil;
import util.Set;

/**
 * @deprecated currently not used
 * @version $Id$
 */
public class BigSet implements Cloneable {
  private static int MaxSize = 10000;
  // four rehashings give ~(>) 13440 els., and .75*13440 ~ 10000
  private static int InitialSize = 840; 
  private boolean USEBUFFERS = true;
  private boolean USEGZIP = false; // note that gzip uses buffering.
  private int BUFFERSIZE = 1024;
  
  private int maxSize;      // max size of set before it gets written to disk
  private int initialSize;  // size of set when new one is built
  private String file;      // prefix of file to which it gets written
  private int filePtr;      // suffix of file to which it gets written
  public Set els;           // the actual elements

  // Constructors
  /**
   * @deprecated currently not used
   */
  public BigSet(String file) {
    this(MaxSize, InitialSize, file); 
  }

  /**
   * @deprecated currently not used
   */
  public BigSet(int maxSize, String file) {
    this(maxSize, InitialSize, file);
  }

  /**
   * @deprecated currently not used
   */
  public BigSet(int maxSize, int initialSize, String file) {
    this.maxSize = maxSize;
    this.initialSize = initialSize;
    this.file = file;
    this.filePtr = 0;
    this.els = new Set(initialSize);

    // SZ Feb 24, 2009: useless code?
    /*
    try {
      OutputStream out0 = new FileOutputStream(file + "0");
      OutputStream out1 = new FileOutputStream(file + "1");
      out0.close(); 
      out1.close();
    }
    catch (IOException e) {
    }*/
    try
    {
        new File(file + "0").createNewFile();
        new File(file + "1").createNewFile();
    } catch (IOException e)
    {
        // TODO Auto-generated catch block
        e.printStackTrace();
    }
  }

  public int size() { return this.els.size(); }
  
  /* writes out the set to disk, as elements* & closes file. */
  public void write() throws IOException {
    Enumeration e = this.els.elements();
    OutputStream out = FileUtil.newBZFileOutputStream(this.file + this.filePtr, USEGZIP,
						      USEBUFFERS, BUFFERSIZE, true);
    int size = this.size();
    BigInt[] bA = new BigInt[size];

    for (int i = 0; i < size(); i++) {
      bA[i] = (BigInt)e.nextElement();
    }

    Arrays.sort(bA, 0, size-1);
    
    ByteUtils.writeInt(out, size);
    for (int i = 0; i < size(); i++) {
      // sT.write(out, bA[i]);
    }
    out.close();
    
    // filePtr goes from 0 to 1 & back.
    this.filePtr = (this.filePtr == 0) ? 1 : 0;
  }
 
  /* clears this set and all it's files */
  public void clear() throws IOException {
    this.delete();
    this.els = new Set();
  }

  /* deletes the files associated with this set.  */
  public void delete() throws IOException {
    File f0, f1;
    f0 = new File(this.file + "0");
    f1 = new File(this.file + "1");
    
    f0.delete();
    f1.delete();
    
    this.filePtr = 0;
  }

  public void put(Object key) throws IOException {
    els.put(key);
    if (this.size() >= this.maxSize) {
      write();
      els = new Set (initialSize);
    }
  }
  
  public boolean contains(Object key) {
    return els.contains(key);
  }
  
}
