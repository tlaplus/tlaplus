// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.util;

/** An <code>IdThread</code> is a <code>Thread</code> with an
    integer identifier. */

public class IdThread extends Thread {
    private final int id;
    
    /** Create a new thread with ID <code>id</code>. */
    public IdThread(int id) {
        this.id = id;
    }
   
    /** Return this thread's ID. */
    // This method was originally called getId, but a later
    // version of Java introduced a getId method into the Thread
    // class which returned a long, and it doesn't allow it to be
    // overridden by a method that returns an int.  So 
    // LL changed the return type from int to long on 31 Aug 2007
    // However, apparently a later version of Java complained when
    // its use in class tlc.tool.liveness.LiveWorker assigned
    // its value to an int variable, so it was renamed myGetId.
    // It is used only in LiveWorker.
    public final int myGetId() { // getId() {
        return this.id;
    }

    /** Return the Id of the calling thread. This method
        will result in a <TT>ClassCastException</TT> if
        the calling thread is not of type <TT>IdThread</TT>. */
    public static int GetId() {
        return ((IdThread)Thread.currentThread()).id;
    }

    /** If the calling thread is of type <TT>IdThread</TT>,
        return its ID. Otherwise, return <TT>otherId</TT>. */
    public static int GetId(int otherId) {
        Thread th = Thread.currentThread();
        return (th instanceof IdThread) ? ((IdThread)th).id : otherId;
    }
}
