// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.dfid;

import tlc2.output.EC;
import tlc2.output.MP;
import util.*;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.net.InetAddress;

/**
 * A <code>MemFPIntSet</code> is a subclass of <code>FPIntSet</code>
 * and a memory-based fingerprint set implementations.  As required by
 * <code>FPIntSet</code>, this class must guarantee that its methods
 * are thread-safe.
 */

public class MemFPIntSet extends FPIntSet {
    /**
     * The load factor and initial capacity for the hashtable.
     */
    private static final int MaxLoad = 20;
    private static final int LogInitialCapacity = 16;
    private String metadir;
    private String filename;
    /**
     * The hash table used to represent the set.
     */
    private int[][] table;

    /**
     * The total number of entries in the set.
     */
    private long count;

    /**
     * Rehashes the table when count exceeds this threshold.
     */
    private long threshold;

    /**
     * The bit-mask used in hashing fingerprints.  Relies on two assumptions:
     * (1) table.length is a power of 2.
     * (2) fingerprints are so random that extracting parts of their bits
     * makes a good hash function.
     */
    private int mask;

    /* Constructs a new, empty FPSet.  */
    public MemFPIntSet() {
        this(LogInitialCapacity, MaxLoad);
    }

    /* The following constructor is provided for test programs only. */
    public MemFPIntSet(final int logInitialCapacity, final int maxLoad) {
        final int initialCapacity = 1 << logInitialCapacity;
        this.count = 0;
        this.threshold = ((long) initialCapacity * maxLoad);
        this.table = new int[initialCapacity][];
        this.mask = initialCapacity - 1;
    }

    @Override
    public final void init(final int numThreads, final String metadir, final String filename) {
        this.metadir = metadir;
        this.filename = filename;
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
        for (final int[] ints : this.table) {
            if (ints != null) {
                size += 16 + (ints.length * 4L);
            }
        }
        return size;
    }

    @Override
    public final synchronized void setLeveled(final long fp) {
        final int index = (int) (fp & this.mask);
        final int[] list = this.table[index];

        // Test if the fingerprint is already in the hashtable.
        if (list != null) {
            final int listlen = list.length;
            for (int i = 0; i < listlen; i += 3) {
                final long fp1 = ((long) list[i] << 32) | (list[i + 1] & 0xFFFFFFFFL);
                if (fp1 == fp) {
                    list[i + 2] = (list[i + 2] & ~LeveledMask) | Leveled;
                    return;
                }
            }
        }

        throw new WrongInvocationException("MemFPIntSet.setLeveled: The fp must have been in the set.");
    }

    @Override
    public final synchronized int setStatus(final long fp, final int status) {
        int index = (int) (fp & this.mask);
        int[] list = this.table[index];

        // Test if the fingerprint is already in the hashtable.
        if (list != null) {
            final int listlen = list.length;
            for (int i = 0; i < listlen; i += 3) {
                final long fp1 = ((long) list[i] << 32) | (list[i + 1] & 0xFFFFFFFFL);
                if (fp == fp1) {
                    final int status1 = list[i + 2];
                    list[i + 2] = status1 | status;
                    // System.err.println("setStatus: " + fp + "  " + status1 + " -> " + this.getStatus(fp));
                    return status1;
                }
            }
        }

        if (count >= threshold) {
            // If the threshold is exceeded, rehash the table and recompute
            // the index.
            this.rehash();
            index = (int) (fp & this.mask);
            list = this.table[index];
        }

        // Creates the new entry.
        final int len = (list == null ? 0 : list.length);
        final int[] newList = new int[len + 3];
        if (list != null) System.arraycopy(list, 0, newList, 0, len);
        newList[len] = (int) (fp >>> 32);
        newList[len + 1] = (int) fp;
        newList[len + 2] = (Level << 2) | Leveled | status;
        this.table[index] = newList;
        this.count++;
        // System.err.println("setStatus: " + fp + "  NEW -> " + this.getStatus(fp));
        return NEW;
    }

    @Override
    public final synchronized int getStatus(final long fp) {
        final int index = (int) (fp & this.mask);
        final int[] list = this.table[index];

        // Test if the fingerprint is already in the hashtable.
        if (list != null) {
            final int listlen = list.length;
            for (int i = 0; i < listlen; i += 3) {
                final long fp1 = ((long) list[i] << 32) | (list[i + 1] & 0xFFFFFFFFL);
                if (fp1 == fp) {
                    return list[i + 2];
                }
            }
        }
        return NEW;
    }

    @Override
    public final boolean allLeveled() {
        for (final int[] bucket : this.table) {
            if (bucket != null) {
                for (int j = 0; j < bucket.length; j += 3) {
                    if ((bucket[j + 2] & LeveledMask) != Leveled) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * Rehashes the contents of the hashtable into a hashtable with a
     * larger capacity. This method is called automatically when the
     * number of items in the hashtable exceeds this hashtable's capacity
     * and load factor.
     */
    private void rehash() {
        long min = this.count, max = 0;
        final int[][] oldTable = this.table;
        final int oldCapacity = oldTable.length;
        final int[][] newTable = new int[oldCapacity * 2][];
        final int onebitmask = oldCapacity;

        for (int i = 0; i < oldCapacity; i++) {
            final int[] list = oldTable[i];
            if (list != null) {
                // The entries in list will be distributed over two arrays in
                // the new hash table.
                // count how big each list will be
                int cnt0 = 0;
                int cnt1 = 0;
                final int listlen = list.length;
                if (listlen < min) min = listlen;
                if (listlen > max) max = listlen;
                for (int j = 0; j < listlen; j += 3) {
                    if ((list[j + 1] & onebitmask) == 0)
                        cnt0 += 3;
                    else
                        cnt1 += 3;
                }

                // handle special cases if either list is empty
                if (cnt0 == 0) {
                    newTable[i + oldCapacity] = list;
                } else if (cnt1 == 0) {
                    newTable[i] = list;
                } else {
                    // allocate two new arrays
                    final int[] list0 = new int[cnt0];
                    final int[] list1 = new int[cnt1];

                    // copy the entries from the old list into the two new ones
                    for (int j = 0; j < listlen; j += 3) {
                        if ((list[j + 1] & onebitmask) == 0) {
                            list0[cnt0 - 3] = list[j];
                            list0[cnt0 - 2] = list[j + 1];
                            list0[cnt0 - 1] = list[j + 2];
                            cnt0 -= 3;
                        } else {
                            list1[cnt1 - 3] = list[j];
                            list1[cnt1 - 2] = list[j + 1];
                            list1[cnt1 - 1] = list[j + 2];
                            cnt1 -= 3;
                        }
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
        final String hostname = InetAddress.getLocalHost().getHostName();
        MP.printMessage(EC.TLC_FP_COMPLETED, hostname);
    }

    @Override
    public final long checkFPs() {
        long dis = Long.MAX_VALUE;
        for (int i = 0; i < this.table.length; i++) {
            final int[] bucket = this.table[i];
            if (bucket != null) {
                for (int j = 0; j < bucket.length; j += 3) {
                    for (int k = j + 3; k < bucket.length; k += 3) {
                        final long x = ((long) bucket[j]) << 32 | bucket[j + 1];
                        final long y = ((long) bucket[k]) << 32 | bucket[k + 1];
                        dis = Math.min(dis, Math.abs(x - y));
                    }
                    for (int k = i + 1; k < this.table.length; k++) {
                        final int[] bucket1 = this.table[k];
                        if (bucket1 != null) {
                            for (int m = 0; m < bucket1.length; m += 3) {
                                final long x = ((long) bucket[j]) << 32 | bucket[j + 1];
                                final long y = ((long) bucket1[m]) << 32 | bucket1[m + 1];
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
            for (final int[] bucket : this.table) {
                if (bucket != null) {
                    for (final int k : bucket) {
                        dos.writeInt(k);
                    }
                }
            }
        }
    }

    @Override
    public final void beginChkpt() throws IOException {
        this.beginChkpt(this.filename);
    }

    @Override
    public final void commitChkpt(final String fname) throws IOException {
        final File oldChkpt = new File(this.chkptName(fname, "chkpt"));
        final File newChkpt = new File(this.chkptName(fname, "tmp"));
        if ((oldChkpt.exists() && !oldChkpt.delete()) ||
                !newChkpt.renameTo(oldChkpt)) {
            throw new IOException("MemFPIntSet.commitChkpt: cannot delete " + oldChkpt);
        }
    }

    @Override
    public final void commitChkpt() throws IOException {
        this.commitChkpt(this.filename);
    }

    @Override
    public final void recover(final String fname) throws IOException {
        final BufferedDataInputStream dis =
                new BufferedDataInputStream(this.chkptName(fname, "chkpt"));
        try {
            while (!dis.atEOF()) {
                final int fhi = dis.readInt();
                final int flo = dis.readInt();
                final int level = dis.readInt();

                if (count >= threshold) this.rehash();

                final int index = flo & this.mask;
                final int[] list = this.table[index];
                final int len = (list == null ? 0 : list.length);
                final int[] newList = new int[len + 3];
                if (list != null) System.arraycopy(list, 0, newList, 0, len);
                newList[len] = fhi;
                newList[len + 1] = flo;
                newList[len + 2] = level;
                this.table[index] = newList;
                this.count++;
            }
        } catch (final EOFException e) {
            Assert.fail(EC.SYSTEM_DISK_IO_ERROR_FOR_FILE, "checkpoints");
        }
        dis.close();
    }

    @Override
    public final void recover() throws IOException {
        this.recover(this.filename);
    }

    private String chkptName(final String fname, final String ext) {
        return this.metadir + FileUtil.separator + fname + ".fp." + ext;
    }

}
