// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:35 PST by lamport
//      modified on Tue Feb 13 18:38:24 PST 2001 by yuanyu

package tlc2.util;

import java.io.IOException;

public abstract class ObjectStack {
  /* A stack of objects. */

  protected int len = 0;            // the queue length

  /* Enqueues the state. It is not thread-safe. */
  public final void push(Object state) {
    this.enqueueInner(state);
    this.len++;
  }

  /**
   * Returns the first element in the queue. It returns null if the
   * queue is empty. It is not thread-safe.
   */
  public final Object pop() {
    if (this.len == 0) return null;
    Object state = this.dequeueInner();
    this.len--;
    return state;
  }

  /* Enqueues a state. Wake up any waiting thread. */
  public final synchronized void spush(Object state) {
    this.enqueueInner(state);
    this.len++;
  }

  /* Enqueues a list of states. Wake up any waiting thread. */
  public final synchronized void spush(Object states[]) {
    for (int i = 0; i < states.length; i++) {
      this.enqueueInner(states[i]);
    }
    this.len += states.length;
  }

  /* Return the first element in the queue.  Wait if empty. */
  public final synchronized Object spop() {
    Object state = this.dequeueInner();
    this.len--;
    return state;
  }

  /* Return (up to) the first cnt elements in the queue. Wait if empty. */  
  public final synchronized Object[] spop(int cnt) {
    Object states[] = new Object[cnt];
    int idx;
    for (idx = 0; idx < cnt && this.len > 0; idx++) {
      states[idx] = this.dequeueInner();
      this.len--;
    }
    if (idx == cnt) return states;
      
    Object res[] = new Object[idx];
    for (int i = 0; i < idx; i++) {
      res[i] = states[i];
    }
    return res;
  }

  /* This method returns the size of the state queue. */
  public final int size() { return this.len; }

  /* This method must be implemented in the subclass. */
  abstract void enqueueInner(Object state);

  /* This method must be implemented in the subclass. */
  abstract Object dequeueInner();

  /* Checkpoint. */
  public abstract void beginChkpt() throws IOException;
  public abstract void commitChkpt() throws IOException;
  public abstract void recover() throws IOException;
}
