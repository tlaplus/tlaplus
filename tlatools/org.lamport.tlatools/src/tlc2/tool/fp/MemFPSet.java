// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCTrace;
import util.Assert;
import util.BufferedDataInputStream;
import util.BufferedDataOutputStream;
import util.FileUtil;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.net.InetAddress;
import java.rmi.RemoteException;

/**
 * A <code>MemFPSet</code> is a subclass of <code>FPSet</code> and a
 * memory-based fingerprint set implementations.
 * As required by <code>FPSet</code>, this class must guarantee that
 * its methods are thread-safe.
 */

public class MemFPSet extends FPSet {
    private static final long serialVersionUID = 8950184917272370210L;
    /**
     * The load factor and initial capacity for the hashtable.
     */
    private static final int MaxLoad = 20;
    private static final int LogInitialCapacity = 16;
    private String metadir;
    private String filename;
    /* The hash table used to represent the set.  */
    private long[][] table;

    /* The total number of entries in the set.   */
    private long count;

    /* Rehashes the table when count exceeds this threshold.  */
    private long threshold;

    /**
     * The bit-mask used in hashing fingerprints.  Relies on two assumptions:
     * (1) table.length is a power of 2.
     * (2) fingerprints are so random that extracting parts of their bits
     * makes a good hash function.
     */
    private int mask;

    public MemFPSet() throws RemoteException {
        this(new FPSetConfiguration());
    }

    /* Constructs a new, empty FPSet.  */
    public MemFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
        super(fpSetConfig);
        final int initialCapacity = 1 << LogInitialCapacity;
        this.count = 0;
        this.threshold = (initialCapacity * MaxLoad);
        this.table = new long[initialCapacity][];
        this.mask = initialCapacity - 1;
    }

    @Override
    public final FPSet init(final int numThreads, final String metadir, final String filename) {
        this.metadir = metadir;
        this.filename = filename;
        return this;
    }

    /**
     * Returns the number of fingerprints in this set.
     *
     * @return the number of fingerprints in this set.
     */
    @Override
    public final synchronized long size() {
        return this.count;
    }

    public final synchronized long sizeof() {
        long size = 28; // 8 (ptr table) + 8 (long count) + 8 (long threshold) + 4 (int mask)
        size += 16 + (this.table.length * 8L); // for this.table
        for (final long[] longs : this.table) {
            if (longs != null) {
                size += 16 + (longs.length * 8L);
            }
        }
        return size;
    }

    /**
     * Tests if the specified fingerprint is in this set.  As a side
     * effect, updates the set to contain the fingerprint.
     *
     * @param fp the fingerprint.
     * @return <code>true</code> if the specified fingerprint is
     * in this set; <code>false</code> otherwise.
     * <p>
     */
    @Override
    public synchronized boolean put(final long fp) {
        int index = (int) (fp & this.mask);
        long[] list = this.table[index];

        // Test if the fingerprint is already in the hashtable.
        if (list != null) {
            for (final long l : list) {
                if (l == fp) return true;
            }
        }

        if (count >= threshold) {
            // If the threshold is exceeded, rehash the table and
            // recompute the index.
            rehash();
            index = (int) (fp & this.mask);
            list = this.table[index];
        }

        // Creates the new entry.
        final int len = (list == null ? 0 : list.length);
        final long[] newList = new long[len + 1];
        if (list != null) System.arraycopy(list, 0, newList, 0, len);
        newList[len] = fp;
        this.table[index] = newList;

        this.count++;
        return false;
    }

    @Override
    public synchronized boolean contains(final long fp) {
        final int index = (int) (fp & this.mask);
        final long[] list = this.table[index];

        // Test if the fingerprint is already in the hashtable.
        if (list != null) {
            for (final long l : list) {
                if (l == fp) return true;
            }
        }
        return false;
    }

    /**
     * Rehashes the contents of the hashtable into a hashtable with a
     * larger capacity. This method is called automatically when the
     * number of items in the hashtable exceeds this hashtable's
     * capacity and load factor.
     */
    private void rehash() {
        long min = this.count, max = 0;
        final long[][] oldTable = this.table;
        final int oldCapacity = oldTable.length;
        final long[][] newTable = new long[oldCapacity * 2][];
        final int onebitmask = oldCapacity;

        for (int i = 0; i < oldCapacity; i++) {
            final long[] list = oldTable[i];
            if (list != null) {
                // The entries in list will be distributed over two arrays in
                // the new hash table.
                // count how big each list will be
                int cnt0 = 0;
                int cnt1 = 0;
                final int listlen = list.length;
                if (listlen < min) min = listlen;
                if (listlen > max) max = listlen;
                for (final long value : list) {
                    if ((value & onebitmask) == 0)
                        cnt0++;
                    else
                        cnt1++;
                }

                // handle special cases if either list is empty
                if (cnt0 == 0) {
                    newTable[i + oldCapacity] = list;
                } else if (cnt1 == 0) {
                    newTable[i] = list;
                } else {
                    // allocate two new arrays
                    final long[] list0 = new long[cnt0];
                    final long[] list1 = new long[cnt1];

                    // copy the entries from the old list into the two new ones
                    for (final long l : list) {
                        if ((l & onebitmask) == 0)
                            list0[--cnt0] = l;
                        else
                            list1[--cnt1] = l;
                    }

                    // install new arrays in new table
                    newTable[i] = list0;
                    newTable[i + oldCapacity] = list1;
                }
            }
        }
        this.threshold *= 2;
        this.table = newTable;
        this.mask = newTable.length - 1;
    }

    @Override
    public final void close() throws Exception {
        super.close();

        final String hostname = InetAddress.getLocalHost().getHostName();
        MP.printMessage(EC.TLC_FP_COMPLETED, hostname);
    }

    @Override
    public final long checkFPs() {
        long dis = Long.MAX_VALUE;
        for (int i = 0; i < this.table.length; i++) {
            final long[] bucket = this.table[i];
            if (bucket != null) {
                for (int j = 0; j < bucket.length; j++) {
                    for (int k = j + 1; k < bucket.length; k++) {
                        dis = Math.min(dis, Math.abs(bucket[j] - bucket[k]));
                    }
                    for (int k = i + 1; k < this.table.length; k++) {
                        final long[] bucket1 = this.table[k];
                        if (bucket1 != null) {
                            for (final long l : bucket1) {
                                final long x = bucket[j];
                                final long y = l;
                                final long dis1 = (x > y) ? x - y : y - x;
                                if (dis1 >= 0) {
                                    dis = Math.min(dis, dis1);
                                }
                            }
                        }
                    }
                }
            }
        }
        return dis;
    }

    // Checkpoint.
    @Override
    public final void beginChkpt(final String fname) throws IOException {
        try (final BufferedDataOutputStream dos =
                     new BufferedDataOutputStream(this.chkptName(fname, "tmp"))) {
            for (final long[] bucket : this.table) {
                if (bucket != null) {
                    for (final long l : bucket) {
                        dos.writeLong(l);
                    }
                }
            }
        }
    }

    @Override
    public final void commitChkpt(final String fname) throws IOException {
        final File oldChkpt = new File(this.chkptName(fname, "chkpt"));
        final File newChkpt = new File(this.chkptName(fname, "tmp"));
        if ((oldChkpt.exists() && !oldChkpt.delete()) ||
                !newChkpt.renameTo(oldChkpt)) {
            throw new IOException("MemFPSet.commitChkpt: cannot delete " + oldChkpt);
        }
    }

    @Override
    public final void recover(final String fname) throws IOException {
        final BufferedDataInputStream dis =
                new BufferedDataInputStream(this.chkptName(fname, "chkpt"));
        try {
            while (!dis.atEOF()) {
                Assert.check(!this.put(dis.readLong()), EC.TLC_FP_NOT_IN_SET);
            }
        } catch (final EOFException e) {
            Assert.fail(EC.SYSTEM_DISK_IO_ERROR_FOR_FILE, "checkpoints");
        }
        dis.close();
    }

    @Override
    public final void beginChkpt() throws IOException {
        this.beginChkpt(this.filename);
    }

    @Override
    public final void commitChkpt() throws IOException {
        this.commitChkpt(this.filename);
    }

    @Override
    public final void recover(final TLCTrace trace) throws IOException {
        this.recover(this.filename);
    }

    @Override
    public final void recoverFP(final long fp) {
        Assert.check(!this.put(fp), EC.TLC_FP_NOT_IN_SET);
    }

    private String chkptName(final String fname, final String ext) {
        return this.metadir + FileUtil.separator + fname + ".fp." + ext;
    }

}
