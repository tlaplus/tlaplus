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
package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.util.AdapterFactory;

public class CoverageInformation implements Iterable<CoverageInformationItem> {
	
	private final List<CoverageInformationItem> items = new ArrayList<>();

	private final Map<String, IDocument> nameToDocument = new HashMap<>();

	private final Map<IFile, ModuleCoverageInformation> fileToFCI = new HashMap<>();
	
	public CoverageInformation() {
		// Testing only!
	}
	
	public CoverageInformation(final List<IFile> savedTLAFiles) {
		for (final IFile iFile : savedTLAFiles) {
			try {
				final FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
				final FileEditorInput fei = new FileEditorInput(iFile);
				fileDocumentProvider.connect(fei);
				final IDocument document = fileDocumentProvider.getDocument(fei);
				nameToDocument.put(iFile.getName(), document);
			} catch (final CoreException notExpectedToHappen) {
				notExpectedToHappen.printStackTrace();
			}
		}
	}

	public void add(final CoverageInformationItem item) {
		try {
			final String filename = item.getModuleLocation().source() + ".tla";
			if (nameToDocument.containsKey(filename)) {
				final IDocument document = nameToDocument.get(filename);
				final IRegion region = AdapterFactory.locationToRegion(document , item.getModuleLocation());
				item.setRegion(region);
			}
		} catch (BadLocationException notExpectedToHappen) {
			notExpectedToHappen.printStackTrace();
		}
		
		this.items.add(item);
	}
	
	@Override
	public Iterator<CoverageInformationItem> iterator() {
		return this.items.iterator();
	}

	public boolean isEmpty() {
		return this.items.isEmpty();
	}

	public Object[] toArray() {
		return this.items.toArray();
	}
	
	/**
	 * @return if any item is an instance of CoverageInformationItem and has a count of 0; this mirrors the logic which
	 * 				paints the cells of our statistics coverage table; we do this because there is seemingly a bug
	 *				in our data provider in which {@link TLCModelLaunchDataProvider#hasZeroCoverage()} returns
	 *				true when that's actually incorrect, under the condition of a subsequent model check after a
	 *				model check which did have zero coverage. mku alerted on 20190610.
	 */
	public boolean containsZeroCoverageInformation() {
		return items.stream().filter(item -> 
			((item instanceof CoverageInformationItem) && (((CoverageInformationItem)item).getCount() == 0))
		).findAny().isPresent();
	}
	
	/**
	 * @return true if coverage information pre-dates TLC's new/hierarchical format introduced by the CostModel.
	 */
	public boolean isLegacy() {
		// true if there are no ActionInformationItems.
		return !items.stream().filter(i -> i instanceof ActionInformationItem).findAny().isPresent();
	}

	public boolean has(final IFile iFile) {
		return items.stream().filter(i -> i.isInFile(iFile)).findAny().isPresent();
	}

	public ModuleCoverageInformation projectionFor(final IFile iFile) {
		// The CoverageInformation keeps the CoverageInformationItems for the complete
		// model whereas a FileCoverageInformation keeps the CII for a single module.
		return fileToFCI.computeIfAbsent(iFile, f -> new ModuleCoverageInformation(f, items));
	}
}
