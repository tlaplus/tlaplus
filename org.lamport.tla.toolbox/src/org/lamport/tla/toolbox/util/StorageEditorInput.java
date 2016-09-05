package org.lamport.tla.toolbox.util;

import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;

public class StorageEditorInput extends PlatformObject implements IStorageEditorInput {
    private final IStorage storage;

    public StorageEditorInput(IStorage storage) {
        this.storage = storage;
    }

    @Override
    public IStorage getStorage() {
        return storage;
    }

    @Override
    public ImageDescriptor getImageDescriptor() {
        return null;
    }

    @Override
    public String getName() {
        return getStorage().getName();
    }

    @Override
    public IPersistableElement getPersistable() {
        return null;
    }

    @Override
    public String getToolTipText() {
        return getStorage().getFullPath() != null ? getStorage().getFullPath().toOSString() : getStorage().getName();
    }

    @Override
    public boolean equals(Object object) {
        return object instanceof StorageEditorInput &&
         getStorage().equals(((StorageEditorInput)object).getStorage());
    }

    @Override
    public int hashCode() {
        return getStorage().hashCode();
    }

    @Override
    public boolean exists() {
        return true;
    }
}