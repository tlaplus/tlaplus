// Copyright (c) Jan 30, 2012 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.util;

import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;

import pcal.TLAtoPCalMapping;
import tla2sany.st.Location;

/**
 * A {@link TLAtoPCalMarker} wraps the given {@link IMarker} and provides
 * functionality to map from the TLA+ location the {@link IMarker} points to, to
 * its logical equivalent PCal code.
 * <p>
 * Additionally it is used by the UI (e.g. an {@link IAction}) to indicate to
 * lower layers that they should not link to TLA+, but to PCal.
 * 
 * @author Markus Alexander Kuppe
 */
public class TLAtoPCalMarker implements IMarker {

	private final IMarker delegate;
	private final TLAtoPCalMapping mapping;

	public TLAtoPCalMarker(final IMarker delegate, TLAtoPCalMapping mapping) {
		Assert.isLegal(delegate.getResource() instanceof IFile);
		this.delegate = delegate;
		Assert.isNotNull(mapping);
		this.mapping = mapping;
	}

	/**
	 * @return The {@link pcal.Region} corresponding to this
	 *         {@link TLAtoPCalMarker}. Returns <code>null</code>, if no
	 *         corresponding PCal code can be found.
	 */
	public pcal.Region getRegion() {
		pcal.Region region;
		try {
			Location location = (Location) delegate.getAttribute(TLAMarkerHelper.LOCATION);
			region = location.toRegion();
		} catch (CoreException e) {
			// may not happen! (return null in this case which client code has
			// to handle anyway)
			e.printStackTrace();
			return null;
		}
		final int offset = AdapterFactory.GetLineOfPCalAlgorithm((IFile) delegate.getResource());
		return mapping.mapTLAtoPCalRegion(region, offset);
	}
	
	/**
	 * @see org.eclipse.core.runtime.IAdaptable#getAdapter(java.lang.Class)
	 */
	public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
		return delegate.getAdapter(adapter);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#delete()
	 */
	public void delete() throws CoreException {
		delegate.delete();
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#equals(java.lang.Object)
	 */
	public boolean equals(Object object) {
		return delegate.equals(object);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#exists()
	 */
	public boolean exists() {
		return delegate.exists();
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getAttribute(java.lang.String)
	 */
	public Object getAttribute(String attributeName) throws CoreException {
		return delegate.getAttribute(attributeName);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getAttribute(java.lang.String, int)
	 */
	public int getAttribute(String attributeName, int defaultValue) {
		return delegate.getAttribute(attributeName, defaultValue);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getAttribute(java.lang.String, java.lang.String)
	 */
	public String getAttribute(String attributeName, String defaultValue) {
		return delegate.getAttribute(attributeName, defaultValue);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getAttribute(java.lang.String, boolean)
	 */
	public boolean getAttribute(String attributeName, boolean defaultValue) {
		return delegate.getAttribute(attributeName, defaultValue);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getAttributes()
	 */
	public Map<String, Object> getAttributes() throws CoreException {
		return delegate.getAttributes();
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getAttributes(java.lang.String[])
	 */
	public Object[] getAttributes(String[] attributeNames) throws CoreException {
		return delegate.getAttributes(attributeNames);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getCreationTime()
	 */
	public long getCreationTime() throws CoreException {
		return delegate.getCreationTime();
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getId()
	 */
	public long getId() {
		return delegate.getId();
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getResource()
	 */
	public IResource getResource() {
		return delegate.getResource();
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#getType()
	 */
	public String getType() throws CoreException {
		return delegate.getType();
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#isSubtypeOf(java.lang.String)
	 */
	public boolean isSubtypeOf(String superType) throws CoreException {
		return delegate.isSubtypeOf(superType);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#setAttribute(java.lang.String, int)
	 */
	public void setAttribute(String attributeName, int value)
			throws CoreException {
		delegate.setAttribute(attributeName, value);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#setAttribute(java.lang.String, java.lang.Object)
	 */
	public void setAttribute(String attributeName, Object value)
			throws CoreException {
		delegate.setAttribute(attributeName, value);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#setAttribute(java.lang.String, boolean)
	 */
	public void setAttribute(String attributeName, boolean value)
			throws CoreException {
		delegate.setAttribute(attributeName, value);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#setAttributes(java.lang.String[], java.lang.Object[])
	 */
	public void setAttributes(String[] attributeNames, Object[] values)
			throws CoreException {
		delegate.setAttributes(attributeNames, values);
	}

	/**
	 * @see org.eclipse.core.resources.IMarker#setAttributes(java.util.Map)
	 */
	public void setAttributes(@SuppressWarnings("rawtypes") Map attributes)
			throws CoreException {
		delegate.setAttributes(attributes);
	}
}
