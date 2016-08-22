package org.lamport.tla.toolbox.ui.handler;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2unicode.TLAUnicode;

/**
 * Parses the current module in the editor
 * @author Ron Pressler (pron)
 * @version $Id$
 */
public class Module2UnicodeHandler extends SaveDirtyEditorAbstractHandler implements IHandler {
	public static final String ID_CONVERT_MODULE_TO_UNICODE = "toolbox.command.module.a2u.active";
	public static final String ID_EXPORT_SPEC_AS_UNICODE = "toolbox.command.module.exportascii.active";
	
    /* (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {
        if (event.getCommand() == null)
        	return null;
        if (!(UIHelper.getActiveEditor() instanceof ITextEditor))
        	return null;
        
        switch (event.getCommand().getId()) {
        case ID_CONVERT_MODULE_TO_UNICODE:
        	convertEditorToUnicode(event);
        	return null;
        	
        case ID_EXPORT_SPEC_AS_UNICODE:
        	exportToASCII(event);
            return null;
            
        default:
        	return null;
        }
    }
    
    private void convertEditorToUnicode(ExecutionEvent event) {
    	final ITextEditor activeEditor = (ITextEditor)UIHelper.getActiveEditor();
    	final IEditorInput editorInput = activeEditor.getEditorInput();
    	if (editorInput instanceof IStorageEditorInput) { // IFileEditorInput
        	// final IStorageEditorInput input1 = (IStorageEditorInput)editorInput;
    		final IDocument doc = activeEditor.getDocumentProvider().getDocument(editorInput);
        	final StringWriter out = new StringWriter();
        	TLAUnicode.convert(true, new StringReader(doc.get()), out);
        	
        	doc.set(out.toString());
        }
    }
    
    private void exportToASCII(ExecutionEvent event) {
    	final ITextEditor activeEditor = (ITextEditor)UIHelper.getActiveEditor();
    	// prompt to save any unsaved resources
        // the module open in the active editor could be dependent upon
        // any open module
        boolean proceed = UIHelper.promptUserForDirtyModules();
        if (!proceed)
            return;
    	
        final Shell shell = UIHelper.getShellProvider().getShell();

        final Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null)
        	return;
        final IResource rootModule = spec.getRootFile(); ToolboxHandle.getRootModule();
        final Path specRootPrefix = Paths.get(ResourceHelper.getParentDirName(rootModule)).normalize().toAbsolutePath();
        
        final IEditorInput editorInput = activeEditor.getEditorInput();
        final IFile file = ((IFileEditorInput) editorInput).getFile();
        
        Path newPath = null;
        while (true) {
            String result = showDialog(shell, ResourceHelper.getParentDirName(file));
            if (result == null)
            	return; // cancelled
            
            newPath = Paths.get(result).normalize().toAbsolutePath();
            // check whether the file is in the same directory as the root module
            if (specRootPrefix.equals(newPath)) {
                MessageDialog.openError(shell, "Wrong location selected",
                        "The provided directory must be different than the specification root file");
                continue;
            }

            if (Files.exists(newPath)) {
            	if (!Files.isDirectory(newPath)) {
                    MessageDialog.openError(shell, "Wrong location selected",
                            "The provided path must be a directory.");
                    continue;
                } else {
            		if (Files.exists(newPath.resolve(rootModule.getName()))) {
            			if (!MessageDialog.openQuestion(shell, "Overwrite file?",
	                        "The provided directory already contains a specification by the same name. The existing file will be overwritten."
	                		+ "\nDo you want to overwrite the file " + newPath.resolve(rootModule.getName()) + "?"))
	                    continue;
            		}
                }
                // overwriting existing file file exists
            } else { // create the directory file
                try {
                    Files.createDirectories(newPath);
                } catch (IOException e) {
                	MessageDialog.openError(shell, "Error creating directory.", "Directory could not be created");
                	continue;
                }
            }

            break;
        } 
        
        if (newPath == null)
        	return;
        for (Module module : spec.getModules()) {
        	final Path inputFile = Paths.get(module.getAbsolutePath());
        	final Path outputFile = newPath.resolve(inputFile.getFileName());
        	
        	TLAUnicode.convert(false, inputFile, outputFile);
        }
    }
    
    private String showDialog(Shell shell, String path) {
    	final DirectoryDialog dialog = new DirectoryDialog(shell, SWT.SAVE);
    	// dialog.setOverwrite(true);
    	dialog.setMessage("Select a directory for the exported spec");
        dialog.setFilterPath(path);
        return dialog.open();
    }

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (UIHelper.getActiveEditor() == null)
			return false;
		return super.isEnabled();
	}
}
