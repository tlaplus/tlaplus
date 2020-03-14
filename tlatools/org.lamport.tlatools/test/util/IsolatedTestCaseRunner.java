/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
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
	
		// Since IsolatedTestCaseRunner runs several isolated tests in a single VM, it
		// is good practice to clean resources before each new test.
		System.gc();
		
		ClassLoader classLoader = IsolatedTestCaseRunner.class.getClassLoader();
		if (classLoader instanceof URLClassLoader) {
			// When run within e.g. Eclipse, the classloader might not be of instance
			// URLClassLoader. In this case, just use the provided class loader which won't
			// isolate tests. A set of tests can thus only be run in a single VM from ant
			// or maven which pass a URLClassLoader.
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

		private final Map<String, Class<?>> cache = new HashMap<>();
		private final Set<String> packages = new HashSet<>();
		
		public IsolatedTestCaseClassLoader(URLClassLoader classLoader) {
			super(classLoader.getURLs());
			
			// All of TLC's java packages. 
			packages.add("tla2sany");
			packages.add("pcal");
			packages.add("util");
			packages.add("tla2tex");
			packages.add("tlc2");
		}

		@Override
		public Class<?> loadClass(String name) throws ClassNotFoundException {
			if (cache.containsKey(name)) {
				// Cache to not load classes twice for a single test case which results in a
				// LinkageError.
				return cache.get(name);
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
