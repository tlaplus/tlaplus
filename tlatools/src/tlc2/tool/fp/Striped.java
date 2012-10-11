// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public class Striped {

	public static Striped readWriteLock(final int lockCnt) {
		return new Striped(lockCnt);
	}

	private final ReadWriteLock[] locks;

	public Striped(int lockCnt) {
		this.locks = new ReadWriteLock[lockCnt];
		for (int i = 0; i < locks.length; i++) {
			locks[i] = new ReentrantReadWriteLock();
		}
	}

	public ReadWriteLock getAt(int lockIndex) {
		return this.locks[lockIndex];
	}

	public int size() {
		return locks.length;
	}
}
