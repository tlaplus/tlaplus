// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:16:00 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool.fp;

import tlc2.output.EC;
import tlc2.tool.TLCTrace;
import tlc2.tool.TLCTrace.Enumerator;
import util.Assert;

import java.io.IOException;
import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

/**
 * An <code>MultiFPSet</code> is a set of 64-bit fingerprints.
 */
@SuppressWarnings("serial")
public class MultiFPSet extends FPSet {

    public static final int MAX_FPBITS = 30;
    public static final int MIN_FPBITS = 0;
    /**
     * Indicates that child {@link FPSet} should allocate the built-in amount of memory
     */
    private static final int MEM_DEFAULT = -1;
    /**
     * Contains all nested {@link FPSet}s
     */
    protected final List<FPSet> sets;

    /**
     * Amount of leftmost bits used to determine nested {@link FPSet}
     */
    protected int fpbits;

    /**
     * Create a MultiFPSet with 2^bits FPSets.
     */
    public MultiFPSet(final FPSetConfiguration fpSetConfiguration) throws RemoteException {
        super(fpSetConfiguration);

        final int bits = fpSetConfiguration.getFpBits();
        long fpMemSize = fpSetConfiguration.getMemoryInBytes();

        // LL modified error message on 7 April 2012
        Assert.check(bits > 0 && bits <= MAX_FPBITS, "Illegal number of FPSets found.");

        if (fpMemSize == MEM_DEFAULT) {
        }

        this.sets = getNestedFPSets(fpSetConfiguration);
        this.fpbits = 64 - bits;
    }

    protected List<FPSet> getNestedFPSets(final FPSetConfiguration fpSetConfiguration) throws RemoteException {
        final List<FPSet> s = new ArrayList<>(fpSetConfiguration.getMultiFPSetCnt());
        for (int i = 0; i < fpSetConfiguration.getMultiFPSetCnt(); i++) {
            s.add(FPSetFactory.getFPSet(new MultiFPSetConfiguration(fpSetConfiguration)));
        }
        return s;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#init(int, java.lang.String, java.lang.String)
     */
    @Override
    public final FPSet init(final int numThreads, final String metadir, final String filename) {
        IntStream.range(0, this.sets.size()).parallel().forEach(i -> {
            try {
                sets.get(i).init(numThreads, metadir, filename + "_" + i);
            } catch (final IOException e) {
                throw new RuntimeException(e);
            }
        });
        return this;
    }


    @Override
    public void incWorkers(final int num) {
        sets.forEach(s -> s.incWorkers(num));
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#size()
     */
    @Override
    public final long size() {
        /* Returns the number of fingerprints in this set. */
        return sets.parallelStream().mapToLong(FPSet::size).sum();
    }

    /**
     * @return Partition given fp into the {@link FPSet} space
     */
    protected FPSet getFPSet(final long fp) {
        // determine corresponding fpset (using unsigned right shift)
        // shifts a zero into the leftmost (msb) position of the first operand for right operand times
        // and cast it to int loosing the leftmost 32 bit
        final int idx = (int) (fp >>> this.fpbits);
        return this.sets.get(idx);
    }

    /**
     * Returns <code>true</code> iff the fingerprint <code>fp</code> is in this
     * set. If the fingerprint is not in the set, it is added to the set as a
     * side-effect.
     *
     * @see tlc2.tool.fp.FPSet#put(long)
     */
    @Override
    public final boolean put(final long fp) throws IOException {
        return getFPSet(fp).put(fp);
    }

    /**
     * Returns <code>true</code> iff the fingerprint <code>fp</code> is in this
     * set.
     *
     * @see tlc2.tool.fp.FPSet#contains(long)
     */
    @Override
    public final boolean contains(final long fp) throws IOException {
        return getFPSet(fp).contains(fp);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#close()
     */
    @Override
    public final void close() throws Exception {
        super.close();

        for (final FPSet fpSet : sets) {
            fpSet.close();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#unexportObject(boolean)
     */
    @Override
    public void unexportObject(final boolean force) throws NoSuchObjectException {
        for (final FPSet fpSet : sets) {
            fpSet.unexportObject(force);
        }
        UnicastRemoteObject.unexportObject(this, force);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#checkFPs()
     */
    @Override
    public final long checkFPs() {
        return sets.parallelStream().mapToLong(s -> {
            try {
                return s.checkFPs();
            } catch (final IOException e) {
                throw new RuntimeException(e);
            }
        }).min().orElse(Long.MAX_VALUE);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#checkInvariant()
     */
    @Override
    public boolean checkInvariant() {
        return sets.parallelStream().allMatch(s -> {
            try {
                return s.checkInvariant();
            } catch (final IOException e) {
                throw new RuntimeException(e);
            }
        });
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#beginChkpt()
     */
    @Override
    public final void beginChkpt() throws IOException {
        for (final FPSet fpSet : sets) {
            fpSet.beginChkpt();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#commitChkpt()
     */
    @Override
    public final void commitChkpt() throws IOException {
        for (final FPSet fpSet : sets) {
            fpSet.commitChkpt();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#recover()
     */
    @Override
    public final void recover(final TLCTrace trace) throws IOException {
        final Enumerator elements = trace.elements();
        while (elements.nextPos() != -1) {
            final long fp = elements.nextFP();
            getFPSet(fp).recoverFP(fp);
        }
        elements.close();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#recoverFP(long)
     */
    @Override
    public final void recoverFP(final long fp) throws IOException {
        Assert.check(!this.put(fp), EC.TLC_FP_NOT_IN_SET);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#beginChkpt(java.lang.String)
     */
    @Override
    public final void beginChkpt(final String filename) {
        IntStream.range(0, this.sets.size()).parallel().forEach(i -> {
            try {
                sets.get(i).beginChkpt(filename + "_" + i);
            } catch (final IOException e) {
                throw new RuntimeException(e);
            }
        });
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#commitChkpt(java.lang.String)
     */
    @Override
    public final void commitChkpt(final String filename) {
        IntStream.range(0, this.sets.size()).parallel().forEach(i -> {
            try {
                sets.get(i).commitChkpt(filename + "_" + i);
            } catch (final IOException e) {
                throw new RuntimeException(e);
            }
        });
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.FPSet#recover(java.lang.String)
     */
    @Override
    public final void recover(final String filename) {
        IntStream.range(0, this.sets.size()).parallel().forEach(i -> {
            try {
                sets.get(i).recover(filename + "_" + i);
            } catch (final IOException e) {
                throw new RuntimeException(e);
            }
        });
    }

    public FPSet[] getFPSets() {
        return sets.toArray(new FPSet[0]);
    }
}
