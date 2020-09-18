package classloadhelper;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

/**
 * Custom class loader for loading classes multiple times within the same JVM.
 * Derived from code written by Lê Anh Quân here (MIT licensed):
 * 	https://github.com/quanla/classreloading
 */
public class DynamicClassLoader extends AggressiveClassLoader {

	/**
	 * Loaders which trigger when Java attempts to load certain paths.
	 */
	private List<Function<Path, Optional<byte[]>>> loaders = new LinkedList<>();

	/**
	 * Initializes a new instance.
	 * @param paths Directory paths to intercept.
	 * @throws RuntimeException If path is not an existing directory.
	 */
	public DynamicClassLoader(Path... paths) throws RuntimeException {
		for (Path path : paths) {
			try {
				loaders.add(DynamicClassLoader.constructLoaderFor(path));
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		}
	}

	/**
	 * Constructs a loader for the given path.
	 * @param path The path for which to construct a loader.
	 * @return A loader for the path.
	 * @throws IOException If path does not exist or is not directory.
	 */
	public static Function<Path, Optional<byte[]>> constructLoaderFor(Path path) throws IOException {
		final File file = path.toFile();
		if (!file.exists()) {
			throw new FileNotFoundException(path.toString());
		} else if (file.isDirectory()) {
			return constructDirLoaderFor(path);
		} else {
			throw new IOException(path.toString());
		}
	}

	/**
	 * Constructs loaders for given directory path.
	 * @param dir Directory path.
	 * @return A loader for the directory path.
	 */
	public static Function<Path, Optional<byte[]>> constructDirLoaderFor(final Path dir) {
		return filepath -> {
			File file = dir.resolve(filepath).toFile();
			if (!file.exists()) {
				return Optional.empty();
			}

			try (FileInputStream stream = new FileInputStream(file)) {
				return Optional.of(readData(stream));
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		};
	}

	@Override
	protected Optional<byte[]> loadNewClass(String name) {
		for (Function<Path, Optional<byte[]>> loader : this.loaders) {
			Optional<byte[]> data = loader.apply(AggressiveClassLoader.toFilePath(name));
			if (data.isPresent()) {
				return data;
			}
		}

		return Optional.empty();
	}

	/**
	 * Reads data from a class file input stream.
	 * @param inputStream Input stream of a class file.
	 * @return The class file as an array of bytes.
	 * @throws IOException If error occurs while reading from stream.
	 */
    public static byte[] readData(InputStream inputStream) throws IOException {
		ByteArrayOutputStream boTemp = null;
        byte[] buffer = null;
		int read;
		buffer = new byte[8192];
		boTemp = new ByteArrayOutputStream();
		while ((read = inputStream.read(buffer, 0, 8192)) > -1) {
			boTemp.write(buffer, 0, read);
		}

		return boTemp.toByteArray();
    }
}
