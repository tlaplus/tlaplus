// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import static org.junit.Assert.fail;

import java.io.IOException;
import java.rmi.RemoteException;
import org.junit.Test;

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
	
	@SuppressWarnings("deprecation")
	private FPSet getFPSet(int mem) throws IOException {
		FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(mem);
		fpSetConfiguration.setRatio(1.0d);
		return getFPSet(fpSetConfiguration);
	}
	
	/**
	 * @see Bug #242 in general/bugzilla/index.html
	 */
	@Test
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
	@Test
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
	@Test
	public void testDiskFPSetIntMinValue() throws RemoteException {
		try {
			getFPSet(Integer.MIN_VALUE);
		} catch (Exception e) {
			// expected to be invalid
			return;
		}
		fail();
	}
	@Test
	public void testDiskFPSetZero() throws RemoteException {
		try {
			getFPSet(0);
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
	@Test
	public void testDiskFPSetOne() throws RemoteException {
		try {
			getFPSet(1);
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
}
