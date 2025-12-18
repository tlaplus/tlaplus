/*******************************************************************************
 * Copyright (c) 2025 NVIDIA Corp. All rights reserved. 
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
package tlc2.debug;

import org.eclipse.lsp4j.debug.Capabilities;

public class TLCCapabilities extends Capabilities {

	public static final Capabilities STEP_BACK = new TLCCapabilities(true);

	public static final Capabilities NO_STEP_BACK = new TLCCapabilities(false);

	/**
	 * The debug adapter supports the 'gotoState' request.
	 * <p>
	 * This is an optional property.
	 */
	private Boolean supportsGotoState;

	/**
	 * The debug adapter supports a (effectful) gotoState request for data hovers.
	 * <p>
	 * This is an optional property.
	 */
	public Boolean getSupportsGotoState() {
		return this.supportsGotoState;
	}

	/**
	 * The debug adapter supports a (effectful) gotoState request for data hovers.
	 * <p>
	 * This is an optional property.
	 */
	public void setSupportsGotoState(final Boolean supportsGotoState) {
		this.supportsGotoState = supportsGotoState;
	}

	public TLCCapabilities() {
		super();
	}

	public TLCCapabilities(boolean reverse) {
		super();
		setSupportsStepBack(reverse);
	}
}
