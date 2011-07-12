package tlc2.tool.distributed.selector;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStreamReader;
import java.io.Reader;

import tlc2.tool.distributed.TLCServer;

public class ScriptableBlockSelectorFactory extends BlockSelectorFactory {
	private static final String SCRIPT_NAME = System.getProperty("tlc2.tool.distributed.selector.script");
	
	public static IBlockSelector getBlockSelector(final TLCServer aTLCServer) {
		if(SCRIPT_NAME != null) {
			BlockSelectorFactory bsf = new ScriptableBlockSelectorFactory();
			return bsf.getSelector(aTLCServer);
		}
		// always return the default BlockSelector by default/in case of error
		return new BlockSelector(aTLCServer);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.selector.BlockSelectorFactory#getSelector(tlc2.tool.distributed.TLCServer)
	 */
	protected IBlockSelector getSelector(final TLCServer aTLCServer) {
		try {
			// create reader out of file
			final File scriptFile = new File(SCRIPT_NAME);
			final Reader aReader = new BufferedReader(new InputStreamReader(new FileInputStream(scriptFile)));
			final String absolutePath = scriptFile.getAbsolutePath();
			// script engine is determined based on file suffix
			final String anEngine = absolutePath.substring(absolutePath.lastIndexOf('.') + 1);
			
			// create script engine and read script file
			final javax.script.ScriptEngineManager manager = new javax.script.ScriptEngineManager();
			final javax.script.ScriptEngine engine = manager.getEngineByName(anEngine);
			engine.eval(aReader);
			
			// make TLCServer object available in script global scope
			engine.put("tlcServer", aTLCServer);

			// returns the script object implementing the IBlockSelector interface
			return ((javax.script.Invocable) engine).getInterface(IBlockSelector.class);
		} catch (javax.script.ScriptException e) {
			e.printStackTrace();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		// always return the default BlockSelector by default/in case of error
		return new BlockSelector(aTLCServer);
	}
}
