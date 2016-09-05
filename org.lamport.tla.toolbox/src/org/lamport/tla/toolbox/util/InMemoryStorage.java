package org.lamport.tla.toolbox.util;

import java.io.ByteArrayInputStream;
import java.io.InputStream;

import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.PlatformObject;

public class InMemoryStorage extends PlatformObject implements IStorage {
	private final String name;
	private final byte[] contents;
	
	public InMemoryStorage(String name, byte[] contents) {
		this.name = name;
		this.contents = contents;
	}

	@Override
	public InputStream getContents() throws CoreException {
		return new ByteArrayInputStream(contents);
	}

	@Override
	public IPath getFullPath() {
		return null;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public boolean isReadOnly() {
		return true;
	}
}
