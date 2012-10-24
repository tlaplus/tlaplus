// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.util;


/**
 * A no-op implementation of {@link ReadersWriterLock}, that does not waste time
 * on locking in a single threaded context.
 */
public class SingleThreadedReadersWriterLock extends ReadersWriterLock {

	/* (non-Javadoc)
	 * @see tlc2.util.ReadersWriterLock#BeginRead()
	 */
	@Override
	public void BeginRead() {
	}

	/* (non-Javadoc)
	 * @see tlc2.util.ReadersWriterLock#EndRead()
	 */
	@Override
	public void EndRead() {
	}

	/* (non-Javadoc)
	 * @see tlc2.util.ReadersWriterLock#BeginWrite()
	 */
	@Override
	public void BeginWrite() {
	}

	/* (non-Javadoc)
	 * @see tlc2.util.ReadersWriterLock#EndWrite()
	 */
	@Override
	public void EndWrite() {
	}
}
