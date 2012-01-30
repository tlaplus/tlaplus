// Copyright (c) Jan 30, 2012 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.util;

import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.texteditor.MarkerUtilities;
import org.lamport.tla.toolbox.tool.ToolboxHandle;

import pcal.TLAtoPCalMapping;

/**
 * @author Markus Alexander Kuppe
 */
public class TLAtoPCalMarker implements IMarker {

	private final IMarker delegate;
	private final TLAtoPCalMapping mapping;

	public TLAtoPCalMarker(IMarker delegate) {
		Assert.isLegal(delegate.getResource() instanceof IFile);
		this.delegate = delegate;
		this.mapping = ToolboxHandle.getCurrentSpec().getTpMapping(delegate.getResource().getName());
		Assert.isNotNull(mapping);
	}

	public pcal.Region getRegion() {
		final pcal.Region region = markerToRegion(delegate);
		final int offset = AdapterFactory.GetLineOfPCalAlgorithm((IFile) delegate.getResource());
		return mapping.mapTLAtoPCalRegion(region, offset);
	}
	
    private pcal.Region markerToRegion(final IMarker marker) {
		final int lineNumber = MarkerUtilities.getLineNumber(marker) - 1;
		// string keys come from plugin.xml files
		final int charStart = marker.getAttribute("toolbox.location.begincolumn", 0) - 1;
		final int charEnd = marker.getAttribute("toolbox.location.endcolumn", 0) - 1;
		return new pcal.Region(lineNumber, charStart, charEnd - charStart);
    }
	
	/**
	 * @param adapter
	 * @return
	 * @see org.eclipse.core.runtime.IAdaptable#getAdapter(java.lang.Class)
	 */
	public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
		return delegate.getAdapter(adapter);
	}

	/**
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#delete()
	 */
	public void delete() throws CoreException {
		delegate.delete();
	}

	/**
	 * @param object
	 * @return
	 * @see org.eclipse.core.resources.IMarker#equals(java.lang.Object)
	 */
	public boolean equals(Object object) {
		return delegate.equals(object);
	}

	/**
	 * @return
	 * @see org.eclipse.core.resources.IMarker#exists()
	 */
	public boolean exists() {
		return delegate.exists();
	}

	/**
	 * @param attributeName
	 * @return
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#getAttribute(java.lang.String)
	 */
	public Object getAttribute(String attributeName) throws CoreException {
		return delegate.getAttribute(attributeName);
	}

	/**
	 * @param attributeName
	 * @param defaultValue
	 * @return
	 * @see org.eclipse.core.resources.IMarker#getAttribute(java.lang.String, int)
	 */
	public int getAttribute(String attributeName, int defaultValue) {
		return delegate.getAttribute(attributeName, defaultValue);
	}

	/**
	 * @param attributeName
	 * @param defaultValue
	 * @return
	 * @see org.eclipse.core.resources.IMarker#getAttribute(java.lang.String, java.lang.String)
	 */
	public String getAttribute(String attributeName, String defaultValue) {
		return delegate.getAttribute(attributeName, defaultValue);
	}

	/**
	 * @param attributeName
	 * @param defaultValue
	 * @return
	 * @see org.eclipse.core.resources.IMarker#getAttribute(java.lang.String, boolean)
	 */
	public boolean getAttribute(String attributeName, boolean defaultValue) {
		return delegate.getAttribute(attributeName, defaultValue);
	}

	/**
	 * @return
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#getAttributes()
	 */
	public Map<String, Object> getAttributes() throws CoreException {
		return delegate.getAttributes();
	}

	/**
	 * @param attributeNames
	 * @return
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#getAttributes(java.lang.String[])
	 */
	public Object[] getAttributes(String[] attributeNames) throws CoreException {
		return delegate.getAttributes(attributeNames);
	}

	/**
	 * @return
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#getCreationTime()
	 */
	public long getCreationTime() throws CoreException {
		return delegate.getCreationTime();
	}

	/**
	 * @return
	 * @see org.eclipse.core.resources.IMarker#getId()
	 */
	public long getId() {
		return delegate.getId();
	}

	/**
	 * @return
	 * @see org.eclipse.core.resources.IMarker#getResource()
	 */
	public IResource getResource() {
		return delegate.getResource();
	}

	/**
	 * @return
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#getType()
	 */
	public String getType() throws CoreException {
		return delegate.getType();
	}

	/**
	 * @param superType
	 * @return
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#isSubtypeOf(java.lang.String)
	 */
	public boolean isSubtypeOf(String superType) throws CoreException {
		return delegate.isSubtypeOf(superType);
	}

	/**
	 * @param attributeName
	 * @param value
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#setAttribute(java.lang.String, int)
	 */
	public void setAttribute(String attributeName, int value)
			throws CoreException {
		delegate.setAttribute(attributeName, value);
	}

	/**
	 * @param attributeName
	 * @param value
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#setAttribute(java.lang.String, java.lang.Object)
	 */
	public void setAttribute(String attributeName, Object value)
			throws CoreException {
		delegate.setAttribute(attributeName, value);
	}

	/**
	 * @param attributeName
	 * @param value
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#setAttribute(java.lang.String, boolean)
	 */
	public void setAttribute(String attributeName, boolean value)
			throws CoreException {
		delegate.setAttribute(attributeName, value);
	}

	/**
	 * @param attributeNames
	 * @param values
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#setAttributes(java.lang.String[], java.lang.Object[])
	 */
	public void setAttributes(String[] attributeNames, Object[] values)
			throws CoreException {
		delegate.setAttributes(attributeNames, values);
	}

	/**
	 * @param attributes
	 * @throws CoreException
	 * @see org.eclipse.core.resources.IMarker#setAttributes(java.util.Map)
	 */
	public void setAttributes(Map<String, ? extends Object> attributes)
			throws CoreException {
		delegate.setAttributes(attributes);
	}
}
