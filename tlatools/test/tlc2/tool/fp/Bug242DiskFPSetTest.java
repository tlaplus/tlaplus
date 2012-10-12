// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;
import java.rmi.RemoteException;

/**
 *
 */
public class Bug242DiskFPSetTest extends AbstractFPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(int)
	 */
	@Override
	protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException {
		return new DummyDiskFPSet(fpSetConfig);
	}
	
	private FPSet getFPSet(int mem) throws IOException {
		return getFPSet(new FPSetConfiguration(mem));
	}
	
	/**
	 * @see http://bugzilla.tlaplus.net/show_bug.cgi?id=242
	 */
	public void testDiskFPSetWithHighMem() throws RemoteException {
		try {
			getFPSet(2097153638);
		} catch (OutOfMemoryError e) {
			// valid case
			return;
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
	public void testDiskFPSetIntMaxValue() throws RemoteException {
		try {
			getFPSet(Integer.MAX_VALUE);
		} catch (OutOfMemoryError e) {
			// valid case
			return;
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
	public void testDiskFPSetIntMinValue() throws RemoteException {
		try {
			getFPSet(Integer.MIN_VALUE);
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
	public void testDiskFPSetZero() throws RemoteException {
		try {
			getFPSet(0);
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
	public void testDiskFPSetOne() throws RemoteException {
		try {
			getFPSet(1);
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
}
