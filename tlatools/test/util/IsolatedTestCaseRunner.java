package util;

import java.lang.reflect.InvocationTargetException;
import java.net.URLClassLoader;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.runner.Description;
import org.junit.runner.Runner;
import org.junit.runner.notification.RunNotifier;
import org.junit.runners.JUnit4;
import org.junit.runners.model.InitializationError;

public class IsolatedTestCaseRunner extends Runner {

	private final JUnit4 delegate;

	public IsolatedTestCaseRunner(final Class<?> testFileClass)
			throws InitializationError, ClassNotFoundException, InstantiationException, IllegalAccessException,
			IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException {
	
		
		ClassLoader classLoader = IsolatedTestCaseRunner.class.getClassLoader();
		if (classLoader instanceof URLClassLoader) {
			classLoader = new IsolatedTestCaseClassLoader((URLClassLoader) classLoader);
		}
		delegate = new JUnit4(classLoader.loadClass(testFileClass.getName()));
	}

	@Override
	public Description getDescription() {
		return delegate.getDescription();
	}

	@Override
	public void run(RunNotifier notifier) {
		delegate.run(notifier);
	}
	
	private class IsolatedTestCaseClassLoader extends URLClassLoader {

		private final Map<String, Object> cache = new HashMap<>();
		private final Set<String> packages = new HashSet<>();
		
		public IsolatedTestCaseClassLoader(URLClassLoader classLoader) {
			super(classLoader.getURLs());
			
			packages.add("tla2sany");
			packages.add("pcal");
			packages.add("util");
			packages.add("tla2tex");
			packages.add("tlc2");
		}

		@Override
		public Class<?> loadClass(String name) throws ClassNotFoundException {
			if (cache.containsKey(name)) {
				// Cache to not load classes twice which results in a LinkageError.
				return (Class<?>) cache.get(name);
			}
			for (final String pkg : packages) {
				if (name.startsWith(pkg)) {
					final Class<?> findClass = findClass(name);
					cache.put(name, findClass);
					return findClass;
				}
			}
			return super.loadClass(name);
		}
	}
}
