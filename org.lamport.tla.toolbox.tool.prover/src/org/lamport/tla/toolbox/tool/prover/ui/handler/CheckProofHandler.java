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
import org.lamport.tla.toolbox.tool.prover.job.ProverJobRule;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.LevelNode;
import tla2sany.semantic.TheoremNode;

/**
 * Checks the proof step currently containing the caret. Does
 * not launch the prover if the caret is not at a step. Instead,
 * it shows a message to the user explaining this. See the comments
 * in the execute method for how it works.
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
         * 5.) Get the LevelNode representing a step or top level use/hide containing the caret,
         *     if the caret is at such a node.
         * 6.) If a LevelNode is not found in step 5, show a message to the user saying
         *     the caret is not at a step and return on this method. If a LevelNode is found
         *     in step 5, the begin line is the begin line of the location of the level node.
         *     If the level node has a proof, the end line is the end line of the proof. If the
         *     level node does not have a proof, the end line is the end line of the level node.
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
        LevelNode nodeToProve = ResourceHelper.getPfStepOrUseHideFromMod(parseResult, moduleName,
                (ITextSelection) editor.getSelectionProvider().getSelection(), document);

        /**********************************************************
         * Step 6                                                 *
         **********************************************************/
        // beginning and ending lines of the region to be checked
        int beginLine = 0;
        int endLine = 0;

        if (nodeToProve == null)
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
            beginLine = nodeToProve.getLocation().beginLine();

            // only TheoremNodes can have proofs
            if (nodeToProve instanceof TheoremNode && ((TheoremNode) nodeToProve).getProof() != null)
            {
                endLine = ((TheoremNode) nodeToProve).getProof().getLocation().endLine();
            } else
            {
                endLine = nodeToProve.getLocation().endLine();
            }
        }

        /***********************************************************
         * Step 7                                                  *
         ***********************************************************/
        ProverJob proverJob = new ProverJob("Prover launched on module " + moduleName + " from line " + beginLine
                + " to line " + endLine, moduleFile, null, null);
        proverJob.setLocation(beginLine, 0, endLine, 0);
        proverJob.setUser(true);
        proverJob.setRule(new ProverJobRule());
        proverJob.schedule();

        return null;
    }
}
