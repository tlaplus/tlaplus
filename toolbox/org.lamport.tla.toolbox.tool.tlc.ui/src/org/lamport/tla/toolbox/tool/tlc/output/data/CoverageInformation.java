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
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.util.AdapterFactory;

import tlc2.tool.coverage.ActionWrapper.Relation;
import util.TLAConstants;

public class CoverageInformation {
	
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
			final String filename = item.getModuleLocation().source() + TLAConstants.Files.TLA_EXTENSION;
			if (nameToDocument.containsKey(filename)) {
				final IDocument document = nameToDocument.get(filename);
				final IRegion region = AdapterFactory.locationToRegion(document , item.getModuleLocation());
				item.setRegion(region);
			}
		} catch (BadLocationException notExpectedToHappen) {
			notExpectedToHappen.printStackTrace();
		}
		
		synchronized (items) {
			this.items.add(item);
		}
	}

	public boolean isEmpty() {
		return this.items.isEmpty();
	}

	/**
	 * CIIs for zero-covered/disabled spec actions (init and next-state relation).
	 */
	public List<ActionInformationItem> getDisabledSpecActions() {
		synchronized (items) {
			return items.stream()
					.filter(item -> ((item instanceof ActionInformationItem)
							&& ((ActionInformationItem) item).getRelation() != Relation.PROP
							&& (((ActionInformationItem) item).getCount() == 0)))
					.map(item -> (ActionInformationItem) item).collect(Collectors.toList());
		}
	}
	
	public boolean hasDisabledSpecActions() {
		synchronized (items) {
			return items.stream()
					.filter(item -> ((item instanceof ActionInformationItem)
							&& ((ActionInformationItem) item).getRelation() != Relation.PROP
							&& (((ActionInformationItem) item).getCount() == 0)))
					.findAny().isPresent();
		}
	}

	public List<ActionInformationItem> getSpecActions() {
		synchronized (items) {
			return items.stream()
					.filter(item -> ((item instanceof ActionInformationItem)
							&& ((ActionInformationItem) item).getRelation() != Relation.PROP))
					.map(item -> (ActionInformationItem) item).collect(Collectors.toList());
		}
	}

	/**
	 * @return true if coverage information pre-dates TLC's new/hierarchical format introduced by the CostModel.
	 */
	public boolean isLegacy() {
		// true if there are no ActionInformationItems.
		synchronized (items) {
			return !items.stream().filter(i -> i instanceof ActionInformationItem).findAny().isPresent();
		}
	}

	public boolean has(final IFile iFile) {
		synchronized (items) {
			return items.stream().filter(i -> i.isInFile(iFile)).findAny().isPresent();
		}
	}

	public ModuleCoverageInformation projectionFor(final IFile iFile) {
		// The CoverageInformation keeps the CoverageInformationItems for the complete
		// model whereas a FileCoverageInformation keeps the CII for a single module.
		return fileToFCI.computeIfAbsent(iFile, f -> new ModuleCoverageInformation(f, items));
	}
}
