// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.distributed.consumer;

import java.util.Random;
import java.util.concurrent.Executor;
import java.util.concurrent.Executors;

public abstract class FaultyConsumer {

	/**
	 * The upper bound for the sleep period between TLCServer connects and
	 * disconnects in seconds.
	 */
	private final int sleepUpperBound = Integer.getInteger(
			FaultyConsumer.class.getName() + ".sleep", 180);
	
	protected final Random rnd = new Random();
	
	protected final Executor executor = Executors.newSingleThreadExecutor();
	
	/**
	 * @param upperBound The upper bound for the thread to sleep
	 * @return The actual sleep time in seconds
	 */
	protected long sleep() {
		long seconds = rnd.nextInt(sleepUpperBound);
		try {
			// add least 1 second
			Thread.sleep((seconds + 1) * 1000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		return seconds;
	}

	/**
	 * @return true iff kill should be executed
	 */
	protected boolean shouldKill() {
		// draw from a uniform distribution
		return rnd.nextBoolean();
	}
}
