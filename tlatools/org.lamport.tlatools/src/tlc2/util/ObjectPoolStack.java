// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:35 PST by lamport  
//      modified on Tue Feb 22 15:59:47 PST 2000 by yuanyu   

package tlc2.util;

import tlc2.output.EC;
import tlc2.output.MP;
import util.FatalException;
import util.FileUtil;

import java.io.File;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

public class ObjectPoolStack {

    private final String filePrefix;
    private final Reader reader;
    private final Writer writer;
    private Object[] buf;
    private int hiPool;
    private boolean isIdle;
    private File poolFile;
    public ObjectPoolStack(final int bufSize, final String filePrefix) {
        this.filePrefix = filePrefix;
        this.buf = new Object[bufSize];
        this.hiPool = 0;
        this.isIdle = true;
        this.reader = new Reader();
        this.writer = new Writer();
        this.poolFile = null;
        this.reader.start();
        this.writer.start();
    }

    public final Object[] write(final Object[] outBuf)
            throws InterruptedException {
        synchronized (this) {
            while (!this.isIdle) this.wait();
        }
        final Object[] res = this.buf;
        this.buf = outBuf;
        this.poolFile = new File(this.filePrefix + this.hiPool++);
        this.isIdle = false;
        this.writer.notify();
        return res;
    }

    public final Object[] read(final Object[] inBuf)
            throws InterruptedException {
        if (this.hiPool == 0) return null;
        synchronized (this) {
            while (!this.isIdle) this.wait();
        }
        final Object[] res = this.buf;
        this.buf = inBuf;
        this.hiPool--;
        if (this.hiPool > 0) {
            this.poolFile = new File(this.filePrefix + (this.hiPool - 1));
            this.isIdle = false;
            this.reader.notify();
        }
        return res;
    }

    public final synchronized void beginChkpt(final ObjectOutputStream oos)
            throws IOException {
        oos.writeInt(this.hiPool);
    }

    /* Note that this method is not synchronized. */
    public final void recover(final ObjectInputStream ois) throws IOException {
        this.hiPool = ois.readInt();
        if (this.hiPool > 0) {
            this.poolFile = new File(this.filePrefix + (this.hiPool - 1));
            this.isIdle = false;
            this.reader.notify();
        }
    }

    class Reader extends Thread {
        @Override
        public void run() {
            try {
                synchronized (this) {
                    while (!Thread.currentThread().isInterrupted()) {
                        while (ObjectPoolStack.this.poolFile == null) {
                            this.wait();
                        }
                        final ObjectInputStream ois = FileUtil.newOBFIS(ObjectPoolStack.this.poolFile);
                        for (int i = 0; i < ObjectPoolStack.this.buf.length; i++) {
                            ObjectPoolStack.this.buf[i] = ois.readObject();
                        }
                        ois.close();
                        ObjectPoolStack.this.poolFile = null;
                        ObjectPoolStack.this.isIdle = true;
                        ObjectPoolStack.this.notify();
                    }
                }
            } catch (final Exception e) {
                MP.printError(EC.SYSTEM_ERROR_WRITING_POOL, e);
                throw new FatalException("SYSTEM_ERROR_WRITING_POOL", e);
            }
        }
    }

    class Writer extends Thread {
        @Override
        public void run() {
            try {
                synchronized (this) {
                    while (!Thread.currentThread().isInterrupted()) {
                        while (ObjectPoolStack.this.poolFile == null) {
                            this.wait();
                        }
                        final ObjectOutputStream oos = FileUtil.newOBFOS(ObjectPoolStack.this.poolFile);
                        for (final Object o : ObjectPoolStack.this.buf) {
                            oos.writeObject(o);
                        }
                        oos.close();
                        ObjectPoolStack.this.poolFile = null;
                        ObjectPoolStack.this.isIdle = true;
                        ObjectPoolStack.this.notify();
                    }
                }
            } catch (final Exception e) {
                MP.printError(EC.SYSTEM_ERROR_READING_POOL, e);
                throw new FatalException("SYSTEM_ERROR_WRITING_POOL", e);
            }
        }
    }

}
