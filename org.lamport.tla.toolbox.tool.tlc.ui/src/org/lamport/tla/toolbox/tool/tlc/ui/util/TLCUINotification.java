/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.Date;

import org.eclipse.core.runtime.Platform;
import org.eclipse.mylyn.commons.notifications.ui.AbstractUiNotification;
import org.eclipse.swt.graphics.Image;

@SuppressWarnings("restriction")
public class TLCUINotification extends AbstractUiNotification {
	
	private final String label;
	private final String description;
	private final Date date;
	
	private Image image;
	private Image kindImage;

	public TLCUINotification(final String label, final String description, final Date date) {
		super("org.lamport.tla.toolbox.tool.tlc.ui.notification.event");
		this.label = label;
		this.description = description;
		this.date = date;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.IAdaptable#getAdapter(java.lang.Class)
	 */
	@Override
	public <T> T getAdapter(Class<T> adapter) {
		return Platform.getAdapterManager().getAdapter(this, adapter);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.mylyn.commons.notifications.core.AbstractNotification#getDate()
	 */
	@Override
	public Date getDate() {
		return date;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.mylyn.commons.notifications.core.AbstractNotification#getDescription()
	 */
	@Override
	public String getDescription() {
		return description;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.mylyn.commons.notifications.core.AbstractNotification#getLabel()
	 */
	@Override
	public String getLabel() {
		return label;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.mylyn.commons.notifications.ui.AbstractUiNotification#getNotificationImage()
	 */
	@Override
	public Image getNotificationImage() {
		return image;
	}
	
	public TLCUINotification setImage(Image image) {
		return this;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.mylyn.commons.notifications.ui.AbstractUiNotification#getNotificationKindImage()
	 */
	@Override
	public Image getNotificationKindImage() {
		return kindImage;
	}

	public TLCUINotification setKindImage(Image image) {
		this.kindImage = image;
		return this;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.mylyn.commons.notifications.ui.AbstractUiNotification#open()
	 */
	@Override
	public void open() {
		// Do nothing
	}
}
