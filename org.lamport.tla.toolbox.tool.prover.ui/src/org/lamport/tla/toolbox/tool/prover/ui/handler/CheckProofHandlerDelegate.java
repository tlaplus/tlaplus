package org.lamport.tla.toolbox.tool.prover.ui.handler;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.spec.parser.ParseResultBroadcaster;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * Checks the proof step currently containing the caret
 * or checks the entire module if the caret is not located at a proof step.
 * 
 * @author Daniel Ricketts
 *
 */
public class CheckProofHandlerDelegate extends AbstractHandler implements IHandler
{
    /**
     * The {@link IDocument} describing the module.
     */
    private IDocument document;

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
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
        // ISelection selection = UIHelper.getActivePage().getSelection();
        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        Assert.isNotNull(editor, "Check proof step handler delegate was called with no active editor. This is a bug.");
        ISelectionProvider selectionProvider = (ISelectionProvider) editor.getAdapter(ISelectionProvider.class);
        Assert.isNotNull(selectionProvider, "Active editor does not have a selection provider. This is a bug.");
        ISelection selection = selectionProvider.getSelection();
        if (selection instanceof ITextSelection)
        {
            ITextSelection textSelection = (ITextSelection) selection;
            IEditorInput edInput = editor.getEditorInput();

            if (edInput instanceof FileEditorInput)
            {

                String moduleName = ResourceHelper.getModuleName(((FileEditorInput) edInput).getFile());

                /*
                 * Create a file document provider for the editor
                 * input. Remember to disconnect it.
                 */
                FileDocumentProvider fdp = new FileDocumentProvider();
                try
                {
                    fdp.connect(edInput);
                    document = fdp.getDocument(edInput);
                } catch (CoreException e)
                {
                    ProverUIActivator.logError("Error connecting file document provider to file for module "
                            + moduleName, e);
                } finally
                {
                    /*
                     * Once the document has been retrieved, the document provider is
                     * not needed. Always disconnect it to avoid a memory leak.
                     * 
                     * Keeping it connected only seems to provide synchronization of
                     * the document with file changes. That is not necessary in this context.
                     */
                    fdp.disconnect(edInput);
                }

                HashMap params = new HashMap();

                /*
                 * Try to retrieve the proof step containing the caret.
                 */
                ParseResult parseResult = ParseResultBroadcaster.getParseResultBroadcaster().getParseResult(moduleName);

                if (parseResult != null)
                {

                    SpecObj specObj = parseResult.getSpecObj();

                    if (specObj == null)
                    {
                        // module not successfully parsed
                        return null;
                    }

                    /*
                     * Retrieve the ModuleNode corresponding to the module in the
                     * editor.
                     */
                    Assert.isNotNull(specObj.getExternalModuleTable());

                    ModuleNode moduleNode = specObj.getExternalModuleTable().getModuleNode(
                            UniqueString.uniqueStringOf(moduleName));
                    if (moduleNode == null)
                    {
                        // nothing to do
                        return null;
                    }

                    TheoremNode[] theorems = moduleNode.getTheorems();

                    TheoremNode stepWithCaret = null;

                    for (int i = 0; i < theorems.length; i++)
                    {
                        TheoremNode theoremNode = theorems[i];

                        if (theoremNode.getLocation().source().equals(moduleName))
                        {
                            /*
                             * Found a theorem in the module.
                             * 
                             * See if it has a step containing the caret.
                             * 
                             * The caret is located at the end of the current
                             * selection if a range of text is selected (highlighted).
                             */
                            TheoremNode step = getStepWithCaret(theoremNode, textSelection.getOffset()
                                    + textSelection.getLength());

                            if (step != null)
                            {
                                // found the step with the caret
                                stepWithCaret = step;
                                break;
                            }
                        }
                    }

                    params.put(CheckProofHandler.PARAM_MODULE_NAME, moduleName);

                    if (stepWithCaret != null)
                    {
                        ProofNode proof = stepWithCaret.getProof();
                        if (proof != null)
                        {
                            /*
                             * The region to check is from the beginning
                             * of the step to the end of the proof.
                             */
                            params
                                    .put(CheckProofHandler.PARAM_BEGIN_LINE, ""
                                            + stepWithCaret.getLocation().beginLine());
                            params.put(CheckProofHandler.PARAM_BEGIN_COLUMN, ""
                                    + stepWithCaret.getLocation().beginColumn());
                            params.put(CheckProofHandler.PARAM_END_LINE, "" + proof.getLocation().endLine());
                            params.put(CheckProofHandler.PARAM_END_COLUMN, "" + proof.getLocation().endColumn());

                        }
                    } else
                    {
                        try
                        {
                            /*
                             * Check the entire module.
                             */
                            params.put(CheckProofHandler.PARAM_BEGIN_LINE, "" + 1);
                            params.put(CheckProofHandler.PARAM_BEGIN_COLUMN, "" + 1);
                            params.put(CheckProofHandler.PARAM_END_LINE, "" + document.getNumberOfLines());
                            /*
                             * IDocument lines are 0-based.
                             */
                            params.put(CheckProofHandler.PARAM_END_COLUMN, ""
                                    + document.getLineInformation(document.getNumberOfLines() - 1).getLength());
                        } catch (BadLocationException e)
                        {
                            ProverUIActivator.logError("Error getting line information of last line of module "
                                    + moduleName, e);
                            return null;
                        }
                    }

                    UIHelper.runCommand(CheckProofHandler.COMMAND_ID, params);
                }
            }
        }

        return null;
    }

    /**
     * For all {@link TheoremNode} in the tree rooted at theoremNode,
     * this returns the {@link TheoremNode} that is first on the line
     * containing the caret, or null if none satisfy that criteria.
     * 
     * @param theoremNode
     * @return
     */
    private TheoremNode getStepWithCaret(TheoremNode theoremNode, int caretOffset)
    {
        try
        {
            /*
             * Get the location of the step.
             * 
             * theoremNode.getTheorem() returns the node
             * corresponding to the statement of the step (or theorem).
             * 
             * Return theoremNode if the caret is on any of the lines
             * of the statement of theoremNode. If the caret is not
             * on any of the lines of the statement of theoremNode, then
             * recursively search for a substep containing the caret.
             */
            Location stepLoc = theoremNode.getTheorem().getLocation();
            /*
             * IDocument lines are 0-based and SANY Location lines
             * are 1-based.
             */
            int caretLine = document.getLineOfOffset(caretOffset) + 1;
            // IRegion stepRegion = AdapterFactory.locationToRegion(document, stepLoc);

            if (stepLoc.beginLine() <= caretLine && stepLoc.endLine() >= caretLine/*stepRegion.getOffset() <= caretOffset && stepRegion.getOffset() + stepRegion.getLength() >= caretOffset*/)
            {
                return theoremNode;
            }

            ThmOrAssumpDefNode defNode = theoremNode.getDef();
            /*
             * According to the comments, defNode can be null.
             */
            if (defNode != null)
            {

            }

            /*
             * Theorem node does not contain the caret.
             * Recursively try to find a sub-step containing
             * the caret if the proof contains the caret.
             */
            ProofNode proof = theoremNode.getProof();
            if (proof != null)
            {
                Location proofLoc = proof.getLocation();
                if (caretLine >= proofLoc.beginColumn() && caretLine <= proofLoc.endLine())
                {
                    if (proof instanceof NonLeafProofNode)
                    {
                        NonLeafProofNode nonLeafProof = (NonLeafProofNode) proof;
                        LevelNode[] steps = nonLeafProof.getSteps();

                        /*
                         * From the documentation of NonLeafProofNode,
                         * a step can be one of four types:
                         * 
                         * DefStepNode
                         * UseOrHideNode
                         * InstanceNode
                         * TheoremNode
                         * 
                         * Only TheoremNode can have a proof. Recursively compute
                         * the proof positions for those steps.
                         */
                        for (int i = 0; i < steps.length; i++)
                        {
                            if (steps[i] instanceof TheoremNode)
                            {
                                TheoremNode node = getStepWithCaret((TheoremNode) steps[i], caretOffset);
                                if (node != null)
                                {
                                    return node;
                                }
                            }
                        }
                    }
                }
            }

        } catch (BadLocationException e)
        {
            ProverUIActivator.logError("Error finding step containing caret.", e);
        }
        return null;
    }
}
