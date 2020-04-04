// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import util.TLCRuntime;
import util.TLCRuntime.ARCH;

public abstract class FPSetFactory {

	/**
	 * System property with which a consumer defines the class name of the
	 * {@link FPSet} implementation to use.
	 */
	public static final String IMPL_PROPERTY = FPSet.class.getName() + ".impl";
	
	private static boolean allocatesOnHeap(final Class<? extends FPSet> clazz) {
		return !OffHeapDiskFPSet.class.isAssignableFrom(clazz);
	}

	public static boolean allocatesOnHeap(final String clazz) {
		try {
			final ClassLoader classLoader = FPSet.class.getClassLoader();
			@SuppressWarnings("unchecked")
			Class<? extends FPSet> cls = (Class<? extends FPSet>) classLoader
					.loadClass(clazz);
			return allocatesOnHeap(cls);
		} catch (ClassNotFoundException e) {
			return false;
		}
	}

	private static boolean supportsArchitecture(String clazz) {
		try {
			final ClassLoader classLoader = FPSet.class.getClassLoader();
			@SuppressWarnings("unchecked")
			Class<? extends FPSet> cls = (Class<? extends FPSet>) classLoader
					.loadClass(clazz);
			return supports32Bits(cls);
		} catch (ClassNotFoundException e) {
			return false;
		}
	}

	private static boolean supports32Bits(final Class<? extends FPSet> clazz) {
		if (TLCRuntime.getInstance().getArchitecture() == TLCRuntime.ARCH.x86
				&& OffHeapDiskFPSet.class.isAssignableFrom(clazz)) {
			return false;
		}
		return true;
	}
	
	private static boolean isDiskFPSet(Class<? extends FPSet> cls) {
		return DiskFPSet.class.isAssignableFrom(cls);
	}

	static boolean isDiskFPSet(final String clazz) {
		try {
			final ClassLoader classLoader = FPSet.class.getClassLoader();
			@SuppressWarnings("unchecked")
			Class<? extends FPSet> cls = (Class<? extends FPSet>) classLoader
					.loadClass(clazz);
			return isDiskFPSet(cls);
		} catch (ClassNotFoundException e) {
			return false;
		}
	}

	/**
	 * @see getFPSet
	 * @return
	 * @throws RemoteException 
	 */
	public static FPSet getFPSet() throws RemoteException {
		return getFPSet(new FPSetConfiguration());
	}

	/**
	 * Creates a new {@link FPSet} depending on what the caller wants.
	 * @param fpBits if 0, a {@link DiskFPSet} will be returned, a {@link MultiFPSet} otherwise.
	 * @param fpMemSizeInBytes
	 * @return
	 * @throws RemoteException
	 */
	public static FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		
		final String implClassname = fpSetConfig.getImplementation();
		
		// fpBits > 0 indicates that the consumer requires a MultiFPSet
		if (fpSetConfig.allowsNesting()) {
			// Pass physical memory instead of logical FP count to adhere to
			// the general FPSet ctor contract.
			// @see http://bugzilla.tlaplus.net/show_bug.cgi?id=290
			return new MultiFPSet(fpSetConfig);
		} else {
			if (implClassname != null) {
				if (supportsArchitecture(implClassname)) {
					return loadImplementation(implClassname, fpSetConfig);
				} else {
					final ARCH architecture = TLCRuntime.getInstance().getArchitecture();
					final String msg = String.format(
							"Selected fingerprint set (set of visited states) %s does not support current architecture %s. "
									+ "Reverting to default fingerprint set. "
									+ "Off-heap memory allocated via -XX:MaxDirectMemorySize flag cannot be used by default "
									+ "fingerprint set and is therefore wasted.",
							implClassname, architecture);
					MP.printWarning(EC.TLC_FEATURE_UNSUPPORTED, msg);
				}
			}
			return new MSBDiskFPSet(fpSetConfig);
		}
	}
	

	/**
	 * Create and *initialize* the set.
	 */
	public static Future<FPSet> getFPSetInitialized(final FPSetConfiguration fpSetConfiguration, final String metadir,
			final String mainFile) {
		final ExecutorService es = Executors.newSingleThreadExecutor();
		return es.submit(new Callable<FPSet>() {
			@Override
			public FPSet call() throws Exception {
				try {
					final FPSet fpSet = FPSetFactory.getFPSet(fpSetConfiguration);
					fpSet.init(TLCGlobals.getNumWorkers(), metadir, mainFile);
					return fpSet;
				} finally {
					es.shutdown();
				}
			}
		});
	}

	/**
	 * @return A list of classes implementing {@link FPSet}. Eventually this
	 *         list should be constructed dynamically during runtime.
	 */
	public static String[] getImplementations() {
		final List<String> l = new ArrayList<String>();
		
		l.add(MSBDiskFPSet.class.getName());
		l.add(LSBDiskFPSet.class.getName());
		l.add(OffHeapDiskFPSet.class.getName());

		return l.toArray(new String[l.size()]);
	}

	/**
	 * @return The default for {@link FPSet#getImplementations()}
	 */
	public static String getImplementationDefault() {
		return MSBDiskFPSet.class.getName();
	}

	/**
	 * @param clazz FPSet implementation to use
	 * @param memory Memory dedicated to the FPSet implementation in MiB
	 * @return
	 */
	public static String getVMArguments(final String clazz, final long memory) {
		if (allocatesOnHeap(clazz)) {
			return "-Xmx" + memory + "m";
		} else {
			return "-XX:MaxDirectMemorySize=" + memory + "m";
		}
	}

	/**
	 * This block of code tries to load the given class with the FPSet class
	 * loader. Thus, the class has to be available to it.
	 * 
	 * @param clazz
	 * @param fpMemSizeInBytes 
	 * @param fpBits 
	 * @return
	 */
	private static FPSet loadImplementation(final String clazz, final FPSetConfiguration fpSetConfig) {
		Exception exp = null;
		try {
			// poor mans version of modularity, booh!
			final ClassLoader classLoader = FPSet.class.getClassLoader();
			final Class<?> factoryClass = classLoader.loadClass(clazz);
			
//			// HACK class loading to pass _non heap_ memory into subclasses of
//			// OffHeapFPSet.
//			if (!allocatesOnHeap(clazz)) {
//				long l = TLCRuntime.getInstance().getNonHeapPhysicalMemory() / (long) LongSize;
//				// divide l among all FPSet instances
//				fpMemSizeInFPs = l >> fpBits; 
//			}

			final Constructor<?> constructor = factoryClass
					.getDeclaredConstructor(new Class[] { FPSetConfiguration.class });
			final Object instance = constructor.newInstance(
					fpSetConfig);
			// sanity check if given class from string implements FPSet
			if (instance instanceof FPSet) {
				return (FPSet) instance;
			}
		} catch (ClassNotFoundException e) {
			exp = e;
		} catch (InstantiationException e) {
			exp = e;
		} catch (IllegalAccessException e) {
			exp = e;
		} catch (SecurityException e) {
			exp = e;
		} catch (NoSuchMethodException e) {
			exp = e;
		} catch (IllegalArgumentException e) {
			exp = e;
		} catch (InvocationTargetException e) {
			exp = e;
		}
		// LL modified error message on 7 April 2012
		MP.printWarning(EC.GENERAL, "unsuccessfully trying to load custom FPSet class: " + clazz, exp);
		return null;
	}
}
