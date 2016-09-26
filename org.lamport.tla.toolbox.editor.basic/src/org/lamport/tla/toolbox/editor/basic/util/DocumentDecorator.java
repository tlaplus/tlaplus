package org.lamport.tla.toolbox.editor.basic.util;


import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.BadPositionCategoryException;
import org.eclipse.jface.text.DocumentRewriteSession;
import org.eclipse.jface.text.DocumentRewriteSessionType;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension;
import org.eclipse.jface.text.IDocumentExtension2;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentExtension4;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.IDocumentPartitioningListener;
import org.eclipse.jface.text.IDocumentRewriteSessionListener;
import org.eclipse.jface.text.IPositionUpdater;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.IRepairableDocument;
import org.eclipse.jface.text.IRepairableDocumentExtension;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;

public class DocumentDecorator implements IDocument, IDocumentExtension, IDocumentExtension2, IDocumentExtension3, IDocumentExtension4, IRepairableDocument, IRepairableDocumentExtension {
	private final IDocument doc;
	
	public DocumentDecorator(IDocument doc) {
		this.doc = doc;
	}

	@Override
	public int hashCode() {
		return doc.hashCode();
	}
	
	@Override
	public String toString() {
		return doc.toString();
	}
	
	@Override 
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (o == this)
			return true;
		return doc.equals(o);
	}
	
	public char getChar(int offset) throws BadLocationException {
		return doc.getChar(offset);
	}

	public int getLength() {
		return doc.getLength();
	}

	public String get() {
		return doc.get();
	}

	public String get(int offset, int length) throws BadLocationException {
		return doc.get(offset, length);
	}

	public void set(String text) {
		doc.set(text);
	}

	public void replace(int offset, int length, String text) throws BadLocationException {
		doc.replace(offset, length, text);
	}

	public void addDocumentListener(IDocumentListener listener) {
		doc.addDocumentListener(listener);
	}

	public void removeDocumentListener(IDocumentListener listener) {
		doc.removeDocumentListener(listener);
	}

	public void addPrenotifiedDocumentListener(IDocumentListener documentAdapter) {
		doc.addPrenotifiedDocumentListener(documentAdapter);
	}

	public void removePrenotifiedDocumentListener(IDocumentListener documentAdapter) {
		doc.removePrenotifiedDocumentListener(documentAdapter);
	}

	public void addPositionCategory(String category) {
		doc.addPositionCategory(category);
	}

	public void removePositionCategory(String category) throws BadPositionCategoryException {
		doc.removePositionCategory(category);
	}

	public String[] getPositionCategories() {
		return doc.getPositionCategories();
	}

	public boolean containsPositionCategory(String category) {
		return doc.containsPositionCategory(category);
	}

	public void addPosition(Position position) throws BadLocationException {
		doc.addPosition(position);
	}

	public void removePosition(Position position) {
		doc.removePosition(position);
	}

	public void addPosition(String category, Position position)
			throws BadLocationException, BadPositionCategoryException {
		doc.addPosition(category, position);
	}

	public void removePosition(String category, Position position) throws BadPositionCategoryException {
		doc.removePosition(category, position);
	}

	public Position[] getPositions(String category) throws BadPositionCategoryException {
		return doc.getPositions(category);
	}

	public boolean containsPosition(String category, int offset, int length) {
		return doc.containsPosition(category, offset, length);
	}

	public int computeIndexInCategory(String category, int offset)
			throws BadLocationException, BadPositionCategoryException {
		return doc.computeIndexInCategory(category, offset);
	}

	public void addPositionUpdater(IPositionUpdater updater) {
		doc.addPositionUpdater(updater);
	}

	public void removePositionUpdater(IPositionUpdater updater) {
		doc.removePositionUpdater(updater);
	}

	public void insertPositionUpdater(IPositionUpdater updater, int index) {
		doc.insertPositionUpdater(updater, index);
	}

	public IPositionUpdater[] getPositionUpdaters() {
		return doc.getPositionUpdaters();
	}

	public String[] getLegalContentTypes() {
		return doc.getLegalContentTypes();
	}

	public String getContentType(int offset) throws BadLocationException {
		return doc.getContentType(offset);
	}

	public ITypedRegion getPartition(int offset) throws BadLocationException {
		return doc.getPartition(offset);
	}

	public ITypedRegion[] computePartitioning(int offset, int length) throws BadLocationException {
		return doc.computePartitioning(offset, length);
	}

	public void addDocumentPartitioningListener(IDocumentPartitioningListener listener) {
		doc.addDocumentPartitioningListener(listener);
	}

	public void removeDocumentPartitioningListener(IDocumentPartitioningListener listener) {
		doc.removeDocumentPartitioningListener(listener);
	}

	public void setDocumentPartitioner(IDocumentPartitioner partitioner) {
		doc.setDocumentPartitioner(partitioner);
	}

	public IDocumentPartitioner getDocumentPartitioner() {
		return doc.getDocumentPartitioner();
	}

	public int getLineLength(int line) throws BadLocationException {
		return doc.getLineLength(line);
	}

	public int getLineOfOffset(int offset) throws BadLocationException {
		return doc.getLineOfOffset(offset);
	}

	public int getLineOffset(int line) throws BadLocationException {
		return doc.getLineOffset(line);
	}

	public IRegion getLineInformation(int line) throws BadLocationException {
		return doc.getLineInformation(line);
	}

	public IRegion getLineInformationOfOffset(int offset) throws BadLocationException {
		return doc.getLineInformationOfOffset(offset);
	}

	public int getNumberOfLines() {
		return doc.getNumberOfLines();
	}

	public int getNumberOfLines(int offset, int length) throws BadLocationException {
		return doc.getNumberOfLines(offset, length);
	}

	public int computeNumberOfLines(String text) {
		return doc.computeNumberOfLines(text);
	}

	public String[] getLegalLineDelimiters() {
		return doc.getLegalLineDelimiters();
	}

	public String getLineDelimiter(int line) throws BadLocationException {
		return doc.getLineDelimiter(line);
	}

	@Deprecated
	public int search(int startOffset, String findString, boolean forwardSearch, boolean caseSensitive,
			boolean wholeWord) throws BadLocationException {
		return doc.search(startOffset, findString, forwardSearch, caseSensitive, wholeWord);
	}

	public boolean isLineInformationRepairNeeded(int offset, int length, String text) throws BadLocationException {
		return ((IRepairableDocumentExtension)doc).isLineInformationRepairNeeded(offset, length, text);
	}

	public String getDefaultLineDelimiter() {
		return ((IDocumentExtension4)doc).getDefaultLineDelimiter();
	}

	public void setInitialLineDelimiter(String lineDelimiter) {
		((IDocumentExtension4)doc).setInitialLineDelimiter(lineDelimiter);
	}

	public long getModificationStamp() {
		return ((IDocumentExtension4)doc).getModificationStamp();
	}

	public void replace(int pos, int length, String text, long modificationStamp) throws BadLocationException {
		((IDocumentExtension4)doc).replace(pos, length, text, modificationStamp);
	}

	public void set(String text, long modificationStamp) {
		((IDocumentExtension4)doc).set(text, modificationStamp);
	}

	public void acceptPostNotificationReplaces() {
		((IDocumentExtension2)doc).acceptPostNotificationReplaces();
	}

	public void ignorePostNotificationReplaces() {
		((IDocumentExtension2)doc).ignorePostNotificationReplaces();
	}

	public void registerPostNotificationReplace(IDocumentListener owner, IReplace replace) {
		((IDocumentExtension)doc).registerPostNotificationReplace(owner, replace);
	}

	public void stopPostNotificationProcessing() {
		((IDocumentExtension)doc).stopPostNotificationProcessing();
	}

	public void resumePostNotificationProcessing() {
		((IDocumentExtension)doc).resumePostNotificationProcessing();
	}

	@Deprecated
	public void startSequentialRewrite(boolean normalized) {
		((IDocumentExtension)doc).startSequentialRewrite(normalized);
	}

	@Deprecated
	public void stopSequentialRewrite() {
		((IDocumentExtension)doc).stopSequentialRewrite();
	}

	public void resumeListenerNotification() {
		((IDocumentExtension2)doc).resumeListenerNotification();
	}

	public void stopListenerNotification() {
		((IDocumentExtension2)doc).stopListenerNotification();
	}

	public ITypedRegion[] computePartitioning(String partitioning, int offset, int length,
			boolean includeZeroLengthPartitions) throws BadLocationException, BadPartitioningException {
		return ((IDocumentExtension3)doc).computePartitioning(partitioning, offset, length, includeZeroLengthPartitions);
	}

	public String getContentType(String partitioning, int offset, boolean preferOpenPartitions)
			throws BadLocationException, BadPartitioningException {
		return ((IDocumentExtension3)doc).getContentType(partitioning, offset, preferOpenPartitions);
	}

	public IDocumentPartitioner getDocumentPartitioner(String partitioning) {
		return ((IDocumentExtension3)doc).getDocumentPartitioner(partitioning);
	}

	public String[] getLegalContentTypes(String partitioning) throws BadPartitioningException {
		return ((IDocumentExtension3)doc).getLegalContentTypes(partitioning);
	}

	public ITypedRegion getPartition(String partitioning, int offset, boolean preferOpenPartitions)
			throws BadLocationException, BadPartitioningException {
		return ((IDocumentExtension3)doc).getPartition(partitioning, offset, preferOpenPartitions);
	}

	public String[] getPartitionings() {
		return ((IDocumentExtension3)doc).getPartitionings();
	}

	public void setDocumentPartitioner(String partitioning, IDocumentPartitioner partitioner) {
		((IDocumentExtension3)doc).setDocumentPartitioner(partitioning, partitioner);
	}

	public void repairLineInformation() {
		((IRepairableDocument)doc).repairLineInformation();
	}

	public final DocumentRewriteSession getActiveRewriteSession() {
		return ((IDocumentExtension4)doc).getActiveRewriteSession();
	}

	public DocumentRewriteSession startRewriteSession(DocumentRewriteSessionType sessionType) {
		return ((IDocumentExtension4)doc).startRewriteSession(sessionType);
	}

	public void stopRewriteSession(DocumentRewriteSession session) {
		((IDocumentExtension4)doc).stopRewriteSession(session);
	}

	public void addDocumentRewriteSessionListener(IDocumentRewriteSessionListener listener) {
		((IDocumentExtension4)doc).addDocumentRewriteSessionListener(listener);
	}

	public void removeDocumentRewriteSessionListener(IDocumentRewriteSessionListener listener) {
		((IDocumentExtension4)doc).removeDocumentRewriteSessionListener(listener);
	}
}
