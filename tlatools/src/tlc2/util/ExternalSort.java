// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.Date;
import java.util.Random;

import util.Assert;

public class ExternalSort {
  public static final int ARRAYSIZE = 10000;
  public static final int BITS = 211;
  public static final String FILE ="test";
  public static final int BUFFERSIZE = 1024;
  public static final int SORTSIZE = 65536;
  public static boolean USEIBUFFERS = true;
  public static boolean USEOBUFFERS = true;
  public static boolean USEGZIP = false;   //note that gzip uses buffering.

  /** in0 and in1 are merged to out.  Input: it is required that in0
      and in1 be streams of ExternalSortables, prefixed by an integer
      indicating the size of the streams, and that if in0 is empty,
      then in1 is also empty.  If in0 is empty, an IOException is
      thrown.  If there is another IO problem, a RuntimeException is
      thrown.  Output: true is returned if in1 is empty, i.e. this was
      a trivial merge; false is returned otherwise. */
  private static boolean mergeStreams(InputStream in0, InputStream in1,
				      OutputStream out, ExternalSortable ex) 
  throws IOException {
    ExternalSortable a0, a1;
    int in0Size;
    int in1Size;
    int in0Pos = 0;
    int in1Pos = 0;
    int lastWrote = -1;
    
    try {
      in0Size = ByteUtils.readInt(in0);
    }
    catch (IOException e) { return true; } // No data, so return

    try {
      in1Size = ByteUtils.readInt(in1);
    }
    catch (IOException e) {
      // Only in0 has any data, so write it and return.
      ByteUtils.writeInt(out, in0Size);
      for (;in0Pos<in0Size; in0Pos++) {
	a0 = ex.read(in0);
	a0.write(out);
      }
      return true;
    }
    // This case should be caught by readInt above
    Assert.check((in0Size > 0) && (in1Size > 0), 
		 "in0size and in1size should both be greater than 0");

    ByteUtils.writeInt(out, in0Size+in1Size);
    a0 = ex; a1 = ex; // To avoid a compiler error re. initialization.
    
    // in0Pos keeps track of how many elements from in0 have been written
    // I only read at the beginning of the loop, so I can never read more
    // than I have (# of elements read <= # of elements written + 1)
    while (in0Pos<in0Size && in1Pos<in1Size) {
      switch (lastWrote) {
      case -1:
	a0 = ex.read(in0); 
	a1 = ex.read(in1); 
	break;
      case 0:
	a0 = ex.read(in0); 
	break;
      case 1:
	a1 = ex.read(in1); 
	break;
      }
      if (a0.compareTo(a1) < 0) {
	a0.write(out);	
	in0Pos++; 
	lastWrote = 0;
      }
      else {
      	a1.write(out);
	in1Pos++;
	lastWrote = 1;
      }
    }

    Assert.check((in0Pos==in0Size) != (in1Pos==in1Size), 
		 "Exactly one of in0Pos==in0Size, in1Pos==in1Size must be true");
    if (in0Pos == in0Size) {
      a1.write(out);
      in1Pos++;
      for (; in1Pos<in1Size; in1Pos++) {
	a1 = ex.read(in1);
	a1.write(out);
      }
    } else {
      a0.write(out);
      in0Pos++;
      for (; in0Pos<in0Size; in0Pos++) {
	a0 = ex.read(in0);
	a0.write(out);
      }
    }
    return false;
  }
     

  /** Sort SORTSIZE chuncks of in, writing the resulting sorted arrays
      (with a size prefix) first to out0, then to out1, and
      alternating.  in should be a stream of ExternalSortable objects
      (no size info).  Once we get an IO error, we sort what we have,
      write it and quit. */
  private static void initialSort(InputStream in, OutputStream out0, 
				 OutputStream out1, ExternalSortable ex) 
  throws IOException {
    ExternalSortable A [] = new ExternalSortable[SORTSIZE];
    int i,j;
    OutputStream out = out0;
    boolean done = false;
    
    do {
      i = 0; // within try block i-1 is the index of the last element in A
             // i is also the number of valid elements in A
      try {
	while (i<SORTSIZE) {
	  A[i] = ex.read(in);
	  i++;
	}
      }
      catch (IOException e) {
	done = true;
      }
      i--; // i is the index of the last element in A
      if (i >= 0) {
	Sort.sortArray(A,0,i);
	ByteUtils.writeInt(out, i+1);
        ExSortUtils.writeArrayOfExternalSortable(A,0,i,out);
	if (out == out0)
	  out = out1;
	else
	  out = out0;
      }
    } while (!done);
  }
  
  /** in0 and in1 are merged to out0 and out1.  in0, in1 should be of
      the form (size A[size])*. out, out0, and out1 will also be such
      sequences.  Returns true if the merging was trivial, i.e. in1
      was empty and false otherwise. */
  private static boolean mergeStreamsToStreams
  (InputStream in0, InputStream in1, OutputStream out0, 
   OutputStream out1, ExternalSortable ex) throws IOException {
    OutputStream out = out0;
    boolean done = false;
    boolean trivialPass = true;

    do {
      done = mergeStreams(in0, in1, out, ex);
      if (!done)
	trivialPass = false;
      if (out == out0)
	out = out1;
      else
	out = out0;
    } while (!done);
    return trivialPass; 
  }
  	
  /** Sort the file with name filename.  The file should be an array
      of ex objects (no size info).  */
  public static void mergeSortFile(String filename, ExternalSortable ex)
  throws IOException {
    File fin;
    InputStream in;
    OutputStream out0, out1;
    
    in = newBZFileIStream(filename);
    out0 = newBZFileOStream(filename + "in0");
    out1 = newBZFileOStream(filename + "in1");
    
    initialSort(in, out0, out1, ex);
    out0.close(); out1.close(); in.close();
    
    fin = new File(filename);
    fin.delete();
    mergeSortedFiles (filename, filename + "in0", filename + "in1", ex);
  }

  /** Sort the files with name filename0, filename1.  Each of the
      files is of the form: (size ExternalSortable)*.  
  */
  public static void mergeSortedFiles(String file, String filename0,
				      String filename1, ExternalSortable ex)
  throws IOException {
    File fin0, fin1, fout0, fout1;
    InputStream in0, in1;
    OutputStream out0, out1;

    boolean done = false;
    do {
      in0 = newBZFileIStream(filename0);
      in1 = newBZFileIStream(filename1);
      out0 = newBZFileOStream(file + "out0");
      out1 = newBZFileOStream(file + "out1");

      done = mergeStreamsToStreams(in0,in1,out0,out1,ex);
      out0.close(); out1.close(); in0.close(); in1.close();

      fin0 = new File (filename0);
      fin1 = new File (filename1);
      fout0 = new File (file + "out0");
      fout1 = new File (file + "out1");
      fin0.delete(); fin1.delete();
      fout0.renameTo(new File(filename0));
      fout1.renameTo(new File(filename1));
    } while (!done);

    in0 = newBZFileIStream(filename0);
    out0 = newBZFileOStream(file);
    try {
      ExSortUtils.appendSizeExternalSortableArrayArray(in0, out0, ex);
    }
    catch (IOException e) {}
    out0.close(); in0.close();

    fin0 = new File (filename0);
    fin1 = new File (filename1);
    fout0 = new File (file + "out0");
    fout1 = new File (file + "out1");

    fin0.delete(); fin1.delete(); fout0.delete(); fout1.delete();
  }

  private static InputStream newBZFileIStream(String file) 
  throws IOException, FileNotFoundException {
    return FileUtil.newBZFileInputStream(file, USEGZIP, USEIBUFFERS, BUFFERSIZE);
  }

  private static OutputStream newBZFileOStream(String file) throws IOException {
    return FileUtil.newBZFileOutputStream(file, USEGZIP, USEOBUFFERS, BUFFERSIZE);
  }

  private static void mainMergeSort(Comparable[] Arr3) 
  throws IOException {
    int i;
    //    System.out.println("\nAttempting Merge Sort \n");

    Sort.sortArray(Arr3,0,ARRAYSIZE-1);
    //    for (i=0; i<ARRAYSIZE; i++) 
    //      System.out.println(Arr3[i]);
  }


  /** Sorts Arr, Arr2 and then merges them; then reads in the merged
      file and checks that it's in order. */
  private static void mainTestMergeFile(BigInt[] Arr, BigInt[] Arr2) 
  throws IOException, FileNotFoundException { 
    FileOutputStream out0 = new FileOutputStream("f0"); 
    FileOutputStream out1 = new FileOutputStream("f1");
    
    long t1 = System.currentTimeMillis();
    mainMergeSort(Arr);
    mainMergeSort(Arr2);
    long t2 = System.currentTimeMillis();
    System.out.println("Internal Sorting took " + (t2 - t1) + "ms");
    
    ExSortUtils.writeSizeArrayOfExternalSortable(Arr,0,Arr.length-1,out0);
    ExSortUtils.writeSizeArrayOfExternalSortable(Arr2,0,Arr2.length-1,out1);

    out0.close();
    out1.close();

    FileInputStream in0 = new FileInputStream("f0");
    FileInputStream in1 = new FileInputStream("f1");

    FileOutputStream out = new FileOutputStream("fout");

    mergeStreams(in0, in1, out, BigInt.BigZero);

    in0 = new FileInputStream("fout");

    int i = ByteUtils.readInt(in0);
    BigInt a = BigInt.BigZero.read(in0);
    for (int j = 1; j < i; j++) {
      BigInt b = a.read(in0);
      if (b.compareTo(a) < 0)
	System.err.println ("Bad merge:  a=" + a + "    b=" + b);
      a = b;
    }
  }

  /** Sorts Arr, Arr2 and then merges them; then reads in the merged
      file and checks that it's in order. */
  private static void mainTestMergeFilesToFiles(BigInt[] Arr) 
  throws IOException, FileNotFoundException { 
    FileOutputStream out0 = new FileOutputStream("fin0"); 
    Date d1, d2;
    
    d1 = new Date();
    mainMergeSort(Arr);
    d2 = new Date();
    
    ExSortUtils.writeArrayOfExternalSortable(Arr,0,Arr.length-1,out0);
    out0.close();

    FileInputStream in0 = new FileInputStream("fin0");

    out0 = new FileOutputStream("fout0");
    FileOutputStream out1 = new FileOutputStream("fout1");

    initialSort(in0, out0, out1, BigInt.BigZero);
    out0.close();
    out1.close();
    in0.close();
    
    in0 = new FileInputStream("fout0");
    FileInputStream in1 = new FileInputStream("fout1");

    out0 = new FileOutputStream("fin0");
    out1 = new FileOutputStream("fin1");
    
    mergeStreamsToStreams(in0,in1,out0,out1, BigInt.BigZero);

    out0.close(); out1.close();
    in0.close(); in1.close();

    in0 = new FileInputStream("fin0");
    ExternalSortable A[];
    try {
      do {
	A = ExSortUtils.readSizeArrayOfExternalSortable(in0, BigInt.BigZero);
	for (int j = 0; j < A.length; j++) {
	  System.out.println(A[j]);
	}
      } while (true);
    } catch (IOException e) {};

    in0 = new FileInputStream("fin1");

    try {
      do {
	A = ExSortUtils.readSizeArrayOfExternalSortable(in0, BigInt.BigZero);
	for (int j = 0; j < A.length; j++) {
	  System.out.println(A[j]);
	}
      } while (true);
    } catch (IOException e) {};
  }
  
  //  public static void mainInitialize(BigInt[] Arr, BigInt[] Arr2, 
  //			    BigInt[] Arr3, BigInt[] Arr4,
  //			    BigInt[] Arr5, BigInt[] Arr6) {
  private static void mainInitialize() throws IOException{
    Random r = new Random();
    OutputStream out = newBZFileOStream("file");

    for (int i = 0; i < ARRAYSIZE; i++) {
      BigInt b = new BigInt(BITS, r);
      b.write(out);
      //      Arr2[i] = Arr[i];
      //      Arr3[i] = Arr[i];
      //      Arr4[i] = Arr[i];
      //      Arr5[i] = Arr[i];
      //      Arr6[i] = Arr[i];
      //   System.out.println(Arr[i]);
    }
    out.close();
    System.out.println("\n \n");
  }

  //  private static void mainTestmergeSortFile(BigInt[] A)
  private static void mainTestmergeSortFile() throws IOException{
    Date d1, d2;
    ExternalSortable[] B;
    InputStream in;
    OutputStream out;
    
    //    for (i=0;i<A.length;i++)
    //      System.out.println(A[i]);
    
    //    d1 = new Date();    
    //    out = newBZFileOStream("file");
    //    Utilities.writeArrayOfExternalSortable(A,0,A.length-1,out);
    //    out.close();
    //    d2 = new Date();
    //    System.out.println("Writing the array took " + 
    //	       (d2.getTime() - d1.getTime()) + "ms");


    //    in = new FileInputStream("file");
    //    B=Utilities.readArrayOfExternalSortable(in, BigInt.BigZero);
    //    for (i=0;i<B.length;i++)
    //      System.out.println(B[i]);

    d1 = new Date();
    mergeSortFile("file", BigInt.BigZero);
    d2 = new Date();
    System.out.println((d2.getTime() - d1.getTime()) + "ms");

    //    in = newBZFileIStream("file");
    //    B=Utilities.readArrayOfExternalSortable(in, BigInt.BigZero);
    //    for (i=1;i<ARRAYSIZE;i++)
    //      if (!B[i].greaterEqual(B[i-1]))
    //      System.out.println("B["+(i-1)+"] = "+B[i-1]+"   and   B["+i+"] = "+B[i]);
  }
  
  public static void main(String argv[]) throws IOException {
    BigInt Arr[] = new BigInt[ARRAYSIZE];
    //    BigInt Arr2[] = new BigInt[ARRAYSIZE];
    //    BigInt Arr3[] = new BigInt[ARRAYSIZE];
    //    BigInt Arr4[] = new BigInt[ARRAYSIZE];
    //    BigInt Arr5[] = new BigInt[ARRAYSIZE];
    BigInt Arr6[] = new BigInt[ARRAYSIZE];
    Date d1, d2;
    
    d1 = new Date();
    //    mainInitialize(Arr,Arr2,Arr3,Arr4,Arr5,Arr6);
    mainInitialize();
    d2 = new Date();
    System.out.println("Initializing 6 arrays took "+(d2.getTime() - d1.getTime()) + "ms");

    /*
    d1 = new Date();
    mainTestMergeFile(Arr, Arr2);
    d2 = new Date();
    System.out.println("Testing Merge File took " + 
		       (d2.getTime() - d1.getTime()) + "ms");
    
    d1 = new Date();
    mainTestMergeFilesToFiles(Arr3);
    d2 = new Date();
    System.out.println("Testing FilesToFiles took " + 
		       (d2.getTime() - d1.getTime()) + "ms");

    System.out.print("External Sort took ");
    mainTestmergeSortFile(Arr);
    System.out.println("Resulting file size is: " + (new File("file")).length());

    USEIBUFFERS=true;
    System.out.print("External Sort w/Input Buffering took ");
    mainTestmergeSortFile(Arr2);
    System.out.println("Resulting file size is: " + (new File("file")).length());
    

    System.out.print("External Sort w/Output Buffering took ");
    USEIBUFFERS=false;
    USEOBUFFERS=true;
    mainTestmergeSortFile(Arr3);
    System.out.println("Resulting file size is: " + (new File("file")).length());
		       */

    System.out.print("External Sort w/ Buffering took ");
    USEIBUFFERS=true;
    USEOBUFFERS=true;
    //    mainTestmergeSortFile(Arr4);
    mainTestmergeSortFile();
    System.out.println("Resulting file size is: " + (new File("file")).length());
    /*
    System.out.print("External Sort w/ Zipping took ");
    USEIBUFFERS=false;
    USEOBUFFERS=false;
    USEGZIP=true;
    mainTestmergeSortFile(Arr5);
    System.out.println("Resulting file size is: " + (new File("file")).length());

    System.out.print("External Sort w/ I/O Buffering and Zipping took ");
    USEIBUFFERS=true;
    USEOBUFFERS=true;
    USEGZIP=true;
    mainTestmergeSortFile(Arr6);
    System.out.println("Resulting file size is: " + (new File("file")).length());
    */
    //    mainInsertSort(Arr, args);
    //    mainInsertMerge(Arr2,args);
    //    mainMergeSort(Arr3,args);
    //    mainTest3approaches(Arr, Arr2, Arr3);

    //    mainBigIntFile(Arr4, Arr5);

    //    d1 = new Date();
    //    mainByteArrayFile(Arr4, Arr5);
    //    d2 = new Date();
    //    System.out.println("ByteArray took " + (d2.getTime() - d1.getTime())
    //		       + "ms");


    //    d1 = new Date();
    //    mainBuffOByteArrayFile(Arr4, Arr5);
    //    d2 = new Date();
    //    System.out.println("BuffOByteArray took " + (d2.getTime() - d1.getTime())
    //		       + "ms");

    //    mainBigIntGZFile(Arr4, Arr5);

    //        mainByteArrayGZFile(Arr4, Arr5);
  }

  private static void mainBuffOByteArrayFile(BigInteger[] Arr4,
					     BigInteger[] Arr5) 
  throws IOException {
    FileOutputStream fos2 = new FileOutputStream(FILE + "BObyte");
    BufferedOutputStream bout2 = new BufferedOutputStream(fos2, BUFFERSIZE);

    for (int i = 0; i < ARRAYSIZE; i++) {
      ByteUtils.writeSizeByteArray(bout2, Arr4[i].toByteArray());
    }
    bout2.close();

    FileInputStream bin2 = new FileInputStream(FILE + "BObyte");

    for (int i = 0; i < ARRAYSIZE; i++) {
      Arr5[i] = ByteUtils.readSizeBigInt(bin2);
    }
    bin2.close();

    for (int i = 0; i < ARRAYSIZE; i++) {
      if (!Arr4[i].equals(Arr5[i])) {
      	System.out.println("Byte: Arr4[" + i + "] differs from Arr5[" + i +"]");
      }
    }
  }  

}
