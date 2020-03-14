// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:39 PST by lamport
//      modified on Mon Jun 19 14:29:07 PDT 2000 by yuanyu
package tlc2.util;

import java.io.Serializable;

import tlc2.output.EC;
import util.Assert;

/** A <code>ReadersWriterLock</code> is a class that can be
    used to synchronize multiple readers and a single writer.
    There are <code>BeginRead</code> and <code>EndRead</code>
    methods that should be called before and after a read-only
    critical section, and <code>BeginWrite</code> and <code>EndWrite</code>
    methods that should be called before and after a critical
    section in which writes are performed. The <code>ReadersWriterLock</code>
    guarantees that no writers will be in the critical section
    while at least one reader is, and vice-versa. It also guarantees
    that at most one writer will be in the critical section at
    a time.<p>
    
    This implementation gives priority to writers. That is, if
    both writers and readers are blocked waiting to enter the
    critical section, then the writer will be given preference.<p>
    
    IMPORTANT NOTE: The methods of a <code>ReadersWriterLock</code>
    are unsynchronized. It is the caller's responsibility to ensure
    that the mutex associated with a <code>ReadersWriterLock</code>
    object <code>rwl</code> is held when any of <code>rwl</code>'s
    methods are called. This requirement is denoted in this module
    by "REQUIRES LL = SELF".

    Written by Allan Heydon and Marc Najork
*/

public class ReadersWriterLock implements Serializable {
    /** Acquire a share of the object's read lock. This call will
        block until no writer holds the lock and there are no writers
        waiting to acquire the lock.<p>
        REQUIRES LL = SELF. */
    public void BeginRead() {
        while (this.hasWriter || this.waitingWriters > 0) {
            try {
                this.wait();
            } catch (InterruptedException e) 
            {
                Assert.fail(EC.SYSTEM_INTERRUPTED);
            }
        }
        this.numReaders++;
    }
    
    /** Release the calling thread's portion of this object's
        read lock.<p>
        REQUIRES LL = SELF. */
    public void EndRead() {
        this.numReaders--;
        if (this.numReaders == 0) {
            this.notifyAll();
        }
    }
    
    /** Acquire this object's write lock. This call will block
        until all readers release their shares of this object's
        read lock.<p>
        REQUIRES LL = SELF. */
    public void BeginWrite() {
        while (this.numReaders > 0 || this.hasWriter) {
            this.waitingWriters++;
            try {
                this.wait();
            } catch (InterruptedException e) {
                Assert.fail(EC.SYSTEM_INTERRUPTED);
            }
            this.waitingWriters--;
        }
        this.hasWriter = true;
    }
    
    /** Release this object's write lock.<p>
        REQUIRES LL = SELF. */
    public void EndWrite() {
        this.hasWriter = false;
        this.notifyAll();
    }
    
    /* The following fields are protected by SELF. */
    private int numReaders = 0;        // # of threads that hold a share of the read lock
    private boolean hasWriter = false; // a thread holds the write lock
    private int waitingWriters = 0;    // # of threads waiting to acquire write lock
}
