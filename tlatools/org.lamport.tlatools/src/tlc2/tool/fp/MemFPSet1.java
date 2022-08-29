// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:15:06 PST by lamport
//      modified on Tue May 15 23:11:51 PDT 2001 by yuanyu

package tlc2.tool.fp;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCTrace;
import tlc2.util.SetOfLong;
import util.Assert;
import util.FileUtil;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.net.InetAddress;
import java.rmi.RemoteException;

/**
 * Alternative implementation
 *
 * @version $Id$
 * @deprecated not used currently
 */
@Deprecated
public final class MemFPSet1 extends FPSet {
    private static final long serialVersionUID = -3147272113595828560L;
    private final SetOfLong set;
    private String metadir;
    private String filename;

    public MemFPSet1(final FPSetConfiguration fpSetConfig) throws RemoteException {
        super(fpSetConfig);
        this.set = new SetOfLong(10001, 0.75f);
    }

    @Override
    public FPSet init(final int numThreads, final String metadir, final String filename) {
        this.metadir = metadir;
        this.filename = filename;
        return this;
    }

    @Override
    public long size() {
        return this.set.size();
    }

    public long sizeof() {
        return 8 + this.set.sizeof();
    }

    @Override
    public synchronized boolean put(final long fp) {
        return this.set.put(fp);
    }

    @Override
    public synchronized boolean contains(final long fp) {
        return this.set.contains(fp);
    }

    @Override
    public void close() throws Exception {
        super.close();

        final String hostname = InetAddress.getLocalHost().getHostName();
        MP.printMessage(EC.TLC_FP_COMPLETED, hostname);
    }

    @Override
    public long checkFPs() {
        return this.set.checkFPs();
    }

    /* Checkpoint. */
    @Override
    public void beginChkpt(final String fname) throws IOException {
        try (final DataOutputStream dos = FileUtil.newDFOS(this.chkptName(fname, "tmp"))) {
            this.set.beginChkpt(dos);
        }
    }

    @Override
    public void commitChkpt(final String fname) throws IOException {
        final File oldChkpt = new File(this.chkptName(fname, "chkpt"));
        final File newChkpt = new File(this.chkptName(fname, "tmp"));
        if ((oldChkpt.exists() && !oldChkpt.delete()) ||
                !newChkpt.renameTo(oldChkpt)) {
            throw new IOException("MemFPSet1.commitChkpt: cannot delete " + oldChkpt);
        }
    }

    @Override
    public void recover(final String fname) throws IOException {
        try (final DataInputStream dis = FileUtil.newDFIS(this.chkptName(fname, "chkpt"))) {
            this.set.recover(dis);
        }
    }

    @Override
    public void beginChkpt() throws IOException {
        this.beginChkpt(this.filename);
    }

    @Override
    public void commitChkpt() throws IOException {
        this.commitChkpt(this.filename);
    }

    @Override
    public void recover(final TLCTrace trace) throws IOException {
        this.recover(this.filename);
    }

    @Override
    public void recoverFP(final long fp) {
        Assert.check(!this.set.put(fp), EC.TLC_FP_NOT_IN_SET);
    }

    private String chkptName(final String fname, final String ext) {
        return this.metadir + FileUtil.separator + fname + ".fp." + ext;
    }

}
