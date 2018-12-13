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
package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.List;

public class ErrorMessage {

	private final String message;
	private final String key;
	private final String modelEditorPageId;
	private final List<String> sections;
	private final String viewerId;

	public ErrorMessage(final String message, final String key, final String modelEditorPageId,
			final List<String> sections, final String viewerId) {
		this.message = message;
		this.key = key;
		this.modelEditorPageId = modelEditorPageId;
		this.sections = sections;
		this.viewerId = viewerId;
	}

	public List<String> getSections() {
		return sections;
	}

	public String getModelEditorPageId() {
		return modelEditorPageId;
	}

	public String getViewerId() {
		return viewerId;
	}

	public String getKey() {
		return key;
	}

	public String getMessage() {
		return message;
	}
}
