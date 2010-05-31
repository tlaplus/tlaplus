package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.prover.job.ProverJob;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.TheoremNode;

/**
 * Checks the proof step currently containing the caret
 * or checks the entire module if the caret is not located at a proof step.
 * 
 * Does nothing if the module has parse errors.
 * 
 * @author Daniel Ricketts
 *
 */
public class CheckProofHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        /*
         * This handler works by scheduling a ProverJob. The ProverJob
         * requires a full file system path to the module being checked
         * and the begin and end lines of the region to be checked. In order
         * to do this, this method will take the following steps:
         * 
         * 1.) Prompt the user to save any modules that are currently open
         *     and unsaved.
         * 2.) Get the active module editor.
         * 3.) Try to obtain a valid parse result for the module in the active editor.
         *     A valid parse result is one that was created since the module was last
         *     written. If there is no valid parse result available, then prompt the user
         *     to parse the module (or maybe just always parse the module). This creates
         *     a valid parse result because the parsing is run in the UI thread.
         * 4.) Check if there are errors in the valid parse result obtained in step 3. If
         *     there are errors, return on this method. There is no need to show a message
         *     to the user in this case because the parse errors view will pop open anyway.
         * 5.) Get the TheoremNode containing the caret, if the TheoremNode is at a caret.
         * 6.) Get the line numbers to send to the prover. If the caret is at a TheoremNode,
         *     then send the beginning line of the TheoremNode and the end line of the proof
         *     of the theorem node. If the caret is not at a TheoremNode, then send the beginning
         *     and end lines of the entire module. In the future, it might be better to show a message
         *     to the user in the second case asking if he wants to check the entire module.
         * 7.) Create and schedule a prover job.
         * 
         * Note that at step 6 ,there are some other possibilities:
         *     -If the caret is not at any proof step, check the whole module.
         *     -If the caret is at a step without a proof, check the whole module.
         *     -If the caret is at a step without a proof, show a message to the user.
         *     -If the caret is at a step without a proof, disable this handler.
         *     -If the caret is not at any proof step, disable this handler.
         *     -If the caret is not at a step with a proof, ask the user if he wants
         *      to check the entire module.
         */
        /**********************************************************
         * Step 1                                                 *
         **********************************************************/
        boolean proceed = UIHelper.promptUserForDirtyModules();
        if (!proceed)
        {
            // the user cancelled
            return null;
        }

        /**********************************************************
         * Step 2                                                 *
         **********************************************************/
        TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
        Assert.isNotNull(editor, "CheckProofStepHandler was executed without a tla editor in focus. This is a bug.");

        /**********************************************************
         * Step 3                                                 *
         **********************************************************/
        IFile moduleFile = ((FileEditorInput) editor.getEditorInput()).getFile();
        ParseResult parseResult = ResourceHelper.getValidParseResult(moduleFile);

        if (parseResult == null)
        {
            parseResult = new ModuleParserLauncher().parseModule(moduleFile, new NullProgressMonitor());
        }

        /**********************************************************
         * Step 4                                                 *
         **********************************************************/
        if (parseResult.getStatus() != IParseConstants.PARSED)
        {
            return null;
        }

        /**********************************************************
         * Step 5                                                 *
         **********************************************************/
        String moduleName = ResourceHelper.getModuleName(moduleFile);
        IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        TheoremNode theoremNode = ResourceHelper.getTheoremNodeWithCaret(parseResult, moduleName,
                (ITextSelection) editor.getSelectionProvider().getSelection(), document);

        /**********************************************************
         * Step 6                                                 *
         **********************************************************/
        // beginning and ending lines of the region to be checked
        int beginLine = 0;
        int endLine = 0;

        if (theoremNode == null || theoremNode.getProof() == null)
        {
            // ask user if he wants to check the entire module
            MessageDialog
                    .openWarning(
                            UIHelper.getShellProvider().getShell(),
                            "Cannot check step",
                            "The caret is not at a step with a proof. It should be at a step with a proof in order to run the command \"Check Proof Step)\"");
            return null;
        } else
        {
            beginLine = theoremNode.getLocation().beginLine();
            endLine = theoremNode.getProof().getLocation().endLine();
        }

        /***********************************************************
         * Step 7                                                  *
         ***********************************************************/
        ProverJob proverJob = new ProverJob("Prover launched on module " + moduleName + " from line " + beginLine
                + " to line " + endLine, moduleFile, null, null, null);
        proverJob.setLocation(beginLine, 0, endLine, 0);
        proverJob.setUser(true);
        proverJob.schedule();

        /*
         * This handler works by launching the command handled by CheckProofHandler.
         * This command has one required parameter, the module name, and four optional
         * parameters, begin line, begin column, end line, end column.
         * 
         * This handler will pass in the four location parameters of step
         * if the caret lies on the same line as a step. It will pass in the
         * four location parameters of the entire module if the caret does
         * not lie on the same line as a step.
         */
        // IEditorPart editor = HandlerUtil.getActiveEditor(event);
        // Assert.isNotNull(editor,
        // "Check proof step handler delegate was called with no active editor. This is a bug.");
        // ISelectionProvider selectionProvider = (ISelectionProvider) editor.getAdapter(ISelectionProvider.class);
        // Assert.isNotNull(selectionProvider, "Active editor does not have a selection provider. This is a bug.");
        // ISelection selection = selectionProvider.getSelection();
        // if (selection instanceof ITextSelection)
        // {
        // ITextSelection textSelection = (ITextSelection) selection;
        // IEditorInput edInput = editor.getEditorInput();
        //
        // if (edInput instanceof FileEditorInput)
        // {
        //
        // IFile moduleFile = ((FileEditorInput) edInput).getFile();
        // String moduleName = ResourceHelper.getModuleName(moduleFile);
        //
        // /*
        // * Create a file document provider for the editor
        // * input. Remember to disconnect it.
        // */
        // FileDocumentProvider fdp = new FileDocumentProvider();
        // try
        // {
        // fdp.connect(edInput);
        // document = fdp.getDocument(edInput);
        // } catch (CoreException e)
        // {
        // ProverUIActivator.logError("Error connecting file document provider to file for module "
        // + moduleName, e);
        // } finally
        // {
        // /*
        // * Once the document has been retrieved, the document provider is
        // * not needed. Always disconnect it to avoid a memory leak.
        // *
        // * Keeping it connected only seems to provide synchronization of
        // * the document with file changes. That is not necessary in this context.
        // */
        // fdp.disconnect(edInput);
        // }
        //
        // HashMap params = new HashMap();
        //
        // /*
        // * Try to retrieve the proof step containing the caret.
        // */
        // ParseResult parseResult = ResourceHelper.getValidParseResult(moduleFile);
        //
        // if (parseResult == null)
        // {
        // /*
        // * No valid parse result available, parse the module.
        // */
        // }
        //
        // if (parseResult != null)
        // {
        //
        // SpecObj specObj = parseResult.getSpecObj();
        //
        // if (specObj == null)
        // {
        // // module not successfully parsed
        // return null;
        // }
        //
        // /*
        // * Retrieve the ModuleNode corresponding to the module in the
        // * editor.
        // */
        // Assert.isNotNull(specObj.getExternalModuleTable());
        //
        // ModuleNode moduleNode = specObj.getExternalModuleTable().getModuleNode(
        // UniqueString.uniqueStringOf(moduleName));
        // if (moduleNode == null)
        // {
        // // nothing to do
        // return null;
        // }
        //
        // TheoremNode[] theorems = moduleNode.getTheorems();
        //
        // TheoremNode stepWithCaret = null;
        //
        // for (int i = 0; i < theorems.length; i++)
        // {
        // TheoremNode theoremNode = theorems[i];
        //
        // if (theoremNode.getLocation().source().equals(moduleName))
        // {
        // /*
        // * Found a theorem in the module.
        // *
        // * See if it has a step containing the caret.
        // *
        // * The caret is located at the end of the current
        // * selection if a range of text is selected (highlighted).
        // */
        // TheoremNode step = UIHelper.getStepWithCaret(theoremNode, textSelection.getOffset()
        // + textSelection.getLength(), document);
        //
        // if (step != null)
        // {
        // // found the step with the caret
        // stepWithCaret = step;
        // break;
        // }
        // }
        // }
        //
        // params.put(CheckProofHandler.PARAM_MODULE_NAME, moduleName);
        //
        // if (stepWithCaret != null)
        // {
        // ProofNode proof = stepWithCaret.getProof();
        // if (proof != null)
        // {
        // /*
        // * The region to check is from the beginning
        // * of the step to the end of the proof.
        // */
        // params
        // .put(CheckProofHandler.PARAM_BEGIN_LINE, ""
        // + stepWithCaret.getLocation().beginLine());
        // params.put(CheckProofHandler.PARAM_BEGIN_COLUMN, ""
        // + stepWithCaret.getLocation().beginColumn());
        // params.put(CheckProofHandler.PARAM_END_LINE, "" + proof.getLocation().endLine());
        // params.put(CheckProofHandler.PARAM_END_COLUMN, "" + proof.getLocation().endColumn());
        //
        // } else
        // {
        // /*
        // * Display a message to the user indicating that there is no
        // * proof for this proof step and then return. The prover
        // * should not be launched.
        // */
        // MessageDialog.openError(UIHelper.getShellProvider().getShell(), "Step without proof.",
        // "The proof step you have selected does not have a proof.");
        // return null;
        // }
        // } else
        // {
        // try
        // {
        // /*
        // * Check the entire module.
        // */
        // params.put(CheckProofHandler.PARAM_BEGIN_LINE, "" + 1);
        // params.put(CheckProofHandler.PARAM_BEGIN_COLUMN, "" + 1);
        // params.put(CheckProofHandler.PARAM_END_LINE, "" + document.getNumberOfLines());
        // /*
        // * IDocument lines are 0-based.
        // */
        // params.put(CheckProofHandler.PARAM_END_COLUMN, ""
        // + document.getLineInformation(document.getNumberOfLines() - 1).getLength());
        // } catch (BadLocationException e)
        // {
        // ProverUIActivator.logError("Error getting line information of last line of module "
        // + moduleName, e);
        // return null;
        // }
        // }
        //
        // UIHelper.runCommand(CheckProofHandler.COMMAND_ID, params);
        // }
        // }
        // }

        return null;
    }
}
