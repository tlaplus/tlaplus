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
package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.List;

public class RootCoverageInformationItem extends CoverageInformationItem {

	public static final int rootLayer = -2;
	
	public RootCoverageInformationItem() {
		layer = rootLayer;
	}
	
	@Override
	protected boolean isRoot() {
		return true;
	}

	@Override
	CoverageInformationItem setRoot(ActionInformationItem root) {
		throw new RuntimeException("Root must not have siblings.");
	}

	@Override
	CoverageInformationItem setSiblings(List<CoverageInformationItem> siblings) {
		throw new RuntimeException("Root must not have siblings.");
	}

	@Override
	boolean hasSiblings() {
		return false;
	}

	@Override
	CoverageInformationItem addChild(CoverageInformationItem child) {
		if (child instanceof ActionInformationItem) {
			return super.addChild(child);
		}
		throw new IllegalArgumentException("Only ActionInformationItem allowed for root.");
	}

	@Override
	CoverageInformationItem setLayer(int i) {
		throw new RuntimeException("Root has fixed layer.");
	}

	@Override
	public CoverageInformationItem getParent() {
		throw new RuntimeException("Root has no parent.");
	}

	@Override
	public ActionInformationItem getRoot() {
		throw new RuntimeException("Root has no ActionInformationItem.");
	}
}
