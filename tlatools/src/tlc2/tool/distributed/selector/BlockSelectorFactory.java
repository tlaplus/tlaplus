package tlc2.tool.distributed.selector;

import tlc2.tool.distributed.TLCServer;

public class BlockSelectorFactory {
	
	/**
	 * Delegate to a custom factory if set
	 */
	private static final String FACTORY_NAME = System.getProperty("tlc2.tool.distributed.selector.factory");

	/**
	 * {@link StaticBlockSelector} system property
	 */
	private static final String STATIC_SELECTOR = System.getProperty("tlc2.tool.distributed.selector.bsf.staticselector");
	/**
	 * {@link BlockSelector} system property
	 */
	private static final String UNLIMITING_SELECTOR = System.getProperty("tlc2.tool.distributed.selector.bsf.unlimitingselector");
	/**
	 * {@link LimitingBlockSelector} system property
	 */
	private static final String LIMITING_SELECTOR = System.getProperty("tlc2.tool.distributed.selector.bsf.limitingselector");
	
	/**
	 * Creates an {@link IBlockSelector} for the given {@link TLCServer}.
	 * @see {@link IBlockSelector}
	 * @param aTLCServer
	 * @return An {@link IBlockSelector} for the given {@link TLCServer}
	 */
	public static IBlockSelector getBlockSelector(final TLCServer aTLCServer) {
		BlockSelectorFactory bsf = new BlockSelectorFactory();
		if(FACTORY_NAME != null) {
			bsf = loadCustomFactory(FACTORY_NAME, bsf);
		}
		return bsf.getSelector(aTLCServer);
	}

	/**
	 * @param clazz Class string to load
	 * @param bsf Default BlockSelectorFactory when loading from String fails
	 * @return A BSF
	 */
	private static BlockSelectorFactory loadCustomFactory(final String clazz, BlockSelectorFactory bsf) {
		try {
			// poor mans version of modularity, booh!
			final ClassLoader classLoader = BlockSelectorFactory.class.getClassLoader();
			final Class<?> factoryClass = classLoader.loadClass(clazz);
			final Object instance = factoryClass.newInstance();
			// sanity check if given class from string implements bsf
			if (instance instanceof BlockSelectorFactory) {
				bsf = (BlockSelectorFactory) instance;
			}
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		} catch (InstantiationException e) {
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		}
		return bsf;
	}
	
	/**
	 * @param aTLCServer
	 * @return An instance of the requested selector type
	 */
	protected IBlockSelector getSelector(final TLCServer aTLCServer) {
		if(Boolean.parseBoolean(STATIC_SELECTOR)) {
			return new StaticBlockSelector(aTLCServer);
		} else if (Boolean.parseBoolean(UNLIMITING_SELECTOR)) {
			return new BlockSelector(aTLCServer);
		} else if (Boolean.parseBoolean(LIMITING_SELECTOR)) {
			return new LimitingBlockSelector(aTLCServer);
		}
		// always return the default BlockSelector by default
		return new StatisticalBlockSelector(aTLCServer);
	}
}
