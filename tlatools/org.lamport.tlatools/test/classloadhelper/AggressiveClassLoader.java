package classloadhelper;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

/**
 * Load all the classes it can, leave rest to Parent ClassLoader.
 * Derived from code written by Lê Anh Quân here (MIT licensed):
 * 	https://github.com/quanla/classreloading
 */
public abstract class AggressiveClassLoader extends ClassLoader {

	/**
	 * Set of classes already loaded by this classloader.
	 */
	Set<String> loadedClasses = new HashSet<>();

	/**
	 * Classes this classloader was unable to load.
	 */
	Set<String> unavailableClasses = new HashSet<>();

	/**
	 * Presumably Java's default classloader, unless this classloader was
	 * loaded by another instance of itself (unlikely unless you're trying
	 * to do something very weird).
	 */
    private ClassLoader parent = AggressiveClassLoader.class.getClassLoader();

    @Override
	public Class<?> loadClass(String name) throws ClassNotFoundException {
		if (loadedClasses.contains(name) || unavailableClasses.contains(name)) {
			return super.loadClass(name); // Use default CL cache
		}

		Optional<byte[]> newClassData = this.loadNewClass(name);
		if (newClassData.isPresent()) {
			loadedClasses.add(name);
			return this.loadClass(newClassData.get(), name);
		} else {
			unavailableClasses.add(name);
			return parent.loadClass(name);
		}
	}

	/**
	 * Retrieves a handle to a loaded class upon request.
	 * @param name The name of the class to load.
	 * @return A handle to the loaded class.
	 */
	public Class<?> load(String name) {
		try {
			return loadClass(name);
		} catch (ClassNotFoundException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * Loads the given class.
	 * @param name The name of the class to load.
	 * @return Bytes from class file.
	 */
	protected abstract Optional<byte[]> loadNewClass(String name);

	/**
	 * Actually loads the class file bytes into memory as a working class.
	 * @param classData Class file byte data.
	 * @param name Name of the class.
	 * @return Handle to the class loaded in memory.
	 */
	public Class<?> loadClass(byte[] classData, String name) {
		Class<?> clazz = defineClass(null, classData, 0, classData.length);
		if (clazz != null) {
			if (clazz.getPackage() == null) {
				definePackage(name.replaceAll("\\.\\w+$", ""), null, null, null, null, null, null, null);
			}
			resolveClass(clazz);
		}
		return clazz;
	}

	/**
	 * Converts ex. tlc2.model.MCError class name to path
	 * tlc2/model/MCError.class
	 * @param name The class name.
	 * @return Path to class file.
	 */
	public static Path toFilePath(String name) {
		return Paths.get(name.replaceAll("\\.", "/") + ".class");
	}
}
