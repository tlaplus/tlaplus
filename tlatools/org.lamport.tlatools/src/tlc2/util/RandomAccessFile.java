// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

import java.io.File;
import java.io.IOException;

/**
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

    public RandomAccessFile(final File file, final String mode) throws IOException {
        super(file, mode);
    }

    public RandomAccessFile(final String name, final String mode) throws IOException {
        super(name, mode);
    }

    @Override
    public void seek(final long pos) throws IOException {
        this.superSeekCnt++;
        final long start = System.currentTimeMillis();
        super.seek(pos);
        this.superSeekTime += System.currentTimeMillis() - start;
    }

    @Override
    public int read() throws IOException {
        this.superReadCnt++;
        final long start = System.currentTimeMillis();
        final int res = super.read();
        this.superReadTime += System.currentTimeMillis() - start;
        return res;
    }

    @Override
    public int read(final byte[] b) throws IOException {
        this.superReadCnt++;
        final long start = System.currentTimeMillis();
        final int res = super.read(b);
        this.superReadTime += System.currentTimeMillis() - start;
        return res;
    }

    @Override
    public int read(final byte[] b, final int off, final int len) throws IOException {
        this.superReadCnt++;
        final long start = System.currentTimeMillis();
        final int res = super.read(b, off, len);
        this.superReadTime += System.currentTimeMillis() - start;
        return res;
    }

    @Override
    public void write(final int b) throws IOException {
        this.superWriteCnt++;
        final long start = System.currentTimeMillis();
        super.write(b);
        this.superWriteTime += System.currentTimeMillis() - start;
    }

    @Override
    public void write(final byte[] b) throws IOException {
        this.superWriteCnt++;
        final long start = System.currentTimeMillis();
        super.write(b);
        this.superWriteTime += System.currentTimeMillis() - start;
    }

    @Override
    public void write(final byte[] b, final int off, final int len) throws IOException {
        this.superWriteCnt++;
        final long start = System.currentTimeMillis();
        super.write(b, off, len);
        this.superWriteTime += System.currentTimeMillis() - start;
    }
}
