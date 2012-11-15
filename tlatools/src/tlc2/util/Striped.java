// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.util;

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

	public void releaseAllLocks() {
		for (int i = size() - 1; i >= 0; i--) {
			this.locks[i].writeLock().unlock();
		}
	}

	public void acquireAllLocks() {
		//TODO find way to do this more efficiently
		for (int i = 0; i < size(); i++) {
			this.locks[i].writeLock().lock();
		}
	}
}
