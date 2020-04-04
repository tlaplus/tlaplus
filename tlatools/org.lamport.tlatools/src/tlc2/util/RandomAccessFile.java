// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.File;
import java.io.IOException;

/**
 * 
 * 
 * @version $Id$
 * Bogus name!
 */
public class RandomAccessFile extends java.io.RandomAccessFile {
    
    public long superSeekCnt = 0L;
    public long superReadCnt = 0L;
    public long superWriteCnt = 0L;
    public long superSeekTime = 0L;
    public long superReadTime = 0L;
    public long superWriteTime = 0L;
    
    public RandomAccessFile(File file, String mode) throws IOException {
        super(file, mode);
    }

    public RandomAccessFile(String name, String mode) throws IOException {
        super(name, mode);
    }

    public void seek(long pos) throws IOException {
        this.superSeekCnt++;
        long start = System.currentTimeMillis();
        super.seek(pos);
        this.superSeekTime += System.currentTimeMillis() - start;
    }
    
    public int read() throws IOException {
        this.superReadCnt++;
        long start = System.currentTimeMillis();
        int res = super.read();
        this.superReadTime += System.currentTimeMillis() - start;
        return res;
    }
    
    public int read(byte[] b) throws IOException {
        this.superReadCnt++;
        long start = System.currentTimeMillis();
        int res = super.read(b);
        this.superReadTime += System.currentTimeMillis() - start;
        return res;
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        this.superReadCnt++;
        long start = System.currentTimeMillis();
        int res = super.read(b, off, len);
        this.superReadTime += System.currentTimeMillis() - start;
        return res;
    }
    
    public void write(int b) throws IOException {
        this.superWriteCnt++;
        long start = System.currentTimeMillis();
        super.write(b);
        this.superWriteTime += System.currentTimeMillis() - start;
    }
    
    public void write(byte[] b) throws IOException {
        this.superWriteCnt++;
        long start = System.currentTimeMillis();
        super.write(b);
        this.superWriteTime += System.currentTimeMillis() - start;
    }    
    
    public void write(byte[] b, int off, int len) throws IOException {
        this.superWriteCnt++;
        long start = System.currentTimeMillis();
        super.write(b, off, len);
        this.superWriteTime += System.currentTimeMillis() - start;
    }
}
