package org.lamport.tla.toolbox.editor.basic.util;

import java.lang.reflect.Field;
import java.util.List;

import org.eclipse.core.commands.operations.IUndoableOperation;
import org.eclipse.text.undo.DocumentUndoManager;

public final class DocumentUndoUtil {
	private DocumentUndoUtil() {}

	static final Class<?> undoableTextChange;
	static final Field fStart;
	static final Field fEnd;
	static final Field fText;
	static final Field fPreservedText;
	static final Class<?> undoableCompoundTextChange;
	static final Field fChanges;

	static {
//		Class<?>[] cs = DocumentUndoManager.class.getDeclaredClasses();

		try {
			undoableTextChange = Class.forName(DocumentUndoManager.class.getName() + "$UndoableTextChange");

			fStart = undoableTextChange.getDeclaredField("fStart");
			fStart.setAccessible(true);
			fEnd = undoableTextChange.getDeclaredField("fEnd");
			fEnd.setAccessible(true);
			fText = undoableTextChange.getDeclaredField("fText");
			fText.setAccessible(true);
			fPreservedText = undoableTextChange.getDeclaredField("fPreservedText");
			fPreservedText.setAccessible(true);
			
			undoableCompoundTextChange = Class.forName(DocumentUndoManager.class.getName() + "$UndoableCompoundTextChange");
			fChanges = undoableCompoundTextChange.getDeclaredField("fChanges");
			fChanges.setAccessible(true);
		} catch (Exception e) {
			throw new AssertionError(e);
		}
	}
	
	public static boolean isCompound(IUndoableOperation undo) {
		return undoableCompoundTextChange.isInstance(undo);
	}
	
	public static int getStart(IUndoableOperation undo) {
		return (Integer)get(undo, fStart);
	}
	
	public static void setStart(IUndoableOperation undo, int value) {
		set(undo, fStart, value);
	}
	
	public static int getEnd(IUndoableOperation undo) {
		return (Integer)get(undo, fEnd);
	}
	
	public static void setEnd(IUndoableOperation undo, int value) {
		set(undo, fEnd, value);
	}
	
	public static String getText(IUndoableOperation undo) {
		return (String)get(undo, fText);
	}
	
	public static void setText(IUndoableOperation undo, String value) {
		set(undo, fText, value);
	}
	
	public static String getPreservedText(IUndoableOperation undo) {
		return (String)get(undo, fPreservedText);
	}
	
	public static void setPreservedText(IUndoableOperation undo, String value) {
		set(undo, fPreservedText, value);
	}
	
	public static List<IUndoableOperation> getChanges(IUndoableOperation compound) {
		if (!isCompound(compound))
			throw new ClassCastException("Undo operation " + compound + " is not of type " + undoableCompoundTextChange.getName());
		return (List<IUndoableOperation>)get(compound, fChanges);
	}
	
	private static Object get(IUndoableOperation obj, Field f) {
		verifyUndoableTextChange(obj);
		try {
			return f.get(obj);
		} catch (ReflectiveOperationException e) {
			throw new AssertionError(e);
		}
	}
	
	private static void set(IUndoableOperation obj, Field f, Object value) {
		verifyUndoableTextChange(obj);
		try {
			f.set(obj, value);
		} catch (ReflectiveOperationException e) {
			throw new AssertionError(e);
		}
	}
	
	private static void verifyUndoableTextChange(IUndoableOperation undo) {
		if (!undoableTextChange.isInstance(undo))
			throw new ClassCastException("Undo operation " + undo + " is not of type " + undoableTextChange.getName());
	}
}
