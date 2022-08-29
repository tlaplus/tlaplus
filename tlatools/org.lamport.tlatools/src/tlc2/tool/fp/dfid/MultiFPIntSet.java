// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:15:53 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool.fp.dfid;

import java.io.IOException;

/**
 * An <code>MultiFPInt</code> is a set of 64-bit fingerprints.
 */
public class MultiFPIntSet extends FPIntSet {

    private final FPIntSet[] sets;
    private final int fpbits;

    public MultiFPIntSet(final int bits) {
        final int len = 1 << bits;
        this.sets = new FPIntSet[len];
        for (int i = 0; i < len; i++) {
            this.sets[i] = new MemFPIntSet();
        }
        this.fpbits = 64 - bits;
    }

    @Override
    public final void init(final int numThreads, final String metadir, final String filename)
            throws IOException {
        for (int i = 0; i < this.sets.length; i++) {
            this.sets[i].init(numThreads, metadir, filename + "_" + i);
        }
    }

    /**
     * Returns the number of fingerprints in this set.
     * Warning: The size is only accurate in single-threaded mode.
     */
    @Override
    public final long size() {
        int sum = 0;
        for (final FPIntSet set : this.sets) {
            sum += set.size();
        }
        return sum;
    }

    @Override
    public final void setLeveled(final long fp) {
        final int idx = (int) (fp >>> this.fpbits);
        this.sets[idx].setLeveled(fp);
    }

    @Override
    public final int setStatus(final long fp, final int status) {
        final int idx = (int) (fp >>> this.fpbits);
        return this.sets[idx].setStatus(fp, status);
    }

    /* Returns the status of fp. */
    @Override
    public final int getStatus(final long fp) {
        final int idx = (int) (fp >>> this.fpbits);
        return this.sets[idx].getStatus(fp);
    }

    @Override
    public final boolean allLeveled() {
        for (final FPIntSet set : this.sets) {
            if (!set.allLeveled()) return false;
        }
        return true;
    }

    /* This is not quite correct. */
    @Override
    public final long checkFPs() throws IOException {
        long res = Long.MIN_VALUE;
        for (final FPIntSet set : this.sets) {
            res = Math.max(res, set.checkFPs());
        }
        return res;
    }

    @Override
    public final void close() throws Exception {
        for (final FPIntSet set : this.sets) {
            set.close();
        }

        super.close();

        for (final FPIntSet set : this.sets) {
            set.close();
        }
    }

    @Override
    public final void beginChkpt() throws IOException {
        for (final FPIntSet set : this.sets) {
            set.beginChkpt();
        }
    }

    @Override
    public final void commitChkpt() throws IOException {
        for (final FPIntSet set : this.sets) {
            set.commitChkpt();
        }
    }

    @Override
    public final void recover() throws IOException {
        for (final FPIntSet set : this.sets) {
            set.recover();
        }
    }

    @Override
    public final void beginChkpt(final String filename) throws IOException {
        for (final FPIntSet set : this.sets) {
            set.beginChkpt(filename);
        }
    }

    @Override
    public final void commitChkpt(final String filename) throws IOException {
        for (final FPIntSet set : this.sets) {
            set.commitChkpt(filename);
        }
    }

    @Override
    public final void recover(final String filename) throws IOException {
        for (final FPIntSet set : this.sets) {
            set.recover(filename);
        }
    }

}
