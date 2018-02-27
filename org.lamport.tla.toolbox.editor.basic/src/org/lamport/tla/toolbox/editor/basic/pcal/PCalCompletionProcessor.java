package org.lamport.tla.toolbox.editor.basic.pcal;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.lamport.tla.toolbox.editor.basic.ToolboxCompletionProcessor;

public class PCalCompletionProcessor extends ToolboxCompletionProcessor implements IContentAssistProcessor {

	public PCalCompletionProcessor() {
		// No sense to add "--algorithm" because the 'PCalCompletionProcessor is only
		// hot when cursor/caret inside a PCal algorithm. Thus "--algorithm" is part of
		// TLACompletionProcessor.
//    	proposals.put(IPCalReservedWords.ALGORITHM, "--algorithm AName {\n}");
    	
		List<CompletionProposalTemplate> templates = new ArrayList<CompletionProposalTemplate>();
		templates.add(new CompletionProposalTemplate("process (ProcName \\in {\"p1\",\"p2\"}) { label: skip; }", 
				IPCalReservedWords.PROCESS, IPCalReservedWords.PROCESS_HELP));
		templates.add(new CompletionProposalTemplate("process (ProcName = Id) { label: skip; }",
				IPCalReservedWords.PROCESS, IPCalReservedWords.PROCESS_HELP));
		proposals.put(IPCalReservedWords.PROCESS, templates);

		templates = new ArrayList<ToolboxCompletionProcessor.CompletionProposalTemplate>();
		templates.add(
				new CompletionProposalTemplate("if (TRUE) { skip; };", "if-then", IPCalReservedWords.IFTHENELSE_HELP));
		templates.add(new CompletionProposalTemplate("if (TRUE) { skip; }; else { skip; };", "if-then-else",
				IPCalReservedWords.IFTHENELSE_HELP));
		templates.add(new CompletionProposalTemplate("if (TRUE) { skip; }; elseif { skip; };", "if-then-elseif",
				IPCalReservedWords.IFTHENELSE_HELP));
		proposals.put(IPCalReservedWords.IF, templates);

		proposals.put(IPCalReservedWords.VARIABLE,
				getSingleProposal("variable x = TRUE;", IPCalReservedWords.VARIABLE, IPCalReservedWords.VARIABLE_HELP));
		proposals.put(IPCalReservedWords.VARIABLES, getSingleProposal("variables x = TRUE ; y \\in {1,2,3} ; z;",
				IPCalReservedWords.VARIABLES, IPCalReservedWords.VARIABLE_HELP));
		proposals.put(IPCalReservedWords.PROCEDURE,
				getSingleProposal("procedure PName (param1, ..., paramN) { label: skip; }", IPCalReservedWords.PROCEDURE,
						IPCalReservedWords.PROCEDURE_HELP));
		proposals.put(IPCalReservedWords.CALL, getSingleProposal("call PName (expr1, ..., exprN)",
				IPCalReservedWords.CALL, IPCalReservedWords.PROCEDURE_HELP));
		proposals.put(IPCalReservedWords.WHILE, getSingleProposal("label: while (TRUE) { skip; };",
				IPCalReservedWords.WHILE, IPCalReservedWords.WHILE_HELP));
		proposals.put(IPCalReservedWords.EITHER, getSingleProposal("either { skip; } or { skip; } or { skip; };",
				IPCalReservedWords.EITHER, IPCalReservedWords.EITHEROR_HELP));
		proposals.put(IPCalReservedWords.ASSERT,
				getSingleProposal("assert TRUE;", IPCalReservedWords.ASSERT, IPCalReservedWords.ASSERT_HELP));
		proposals.put(IPCalReservedWords.GOTO,
				getSingleProposal("goto label;", IPCalReservedWords.GOTO, IPCalReservedWords.GOTO_HELP));
		proposals.put(IPCalReservedWords.PRINT,
				getSingleProposal("print \"msg\";", IPCalReservedWords.PRINT, IPCalReservedWords.PRINT_HELP));
		proposals.put(IPCalReservedWords.WITH, getSingleProposal("with ( i \\in {1,2,3} ) { skip; }",
				IPCalReservedWords.WITH, IPCalReservedWords.WITH_HELP));
		proposals.put(IPCalReservedWords.MACRO, getSingleProposal("macro P(param1, ... , paramN) { skip; }",
				IPCalReservedWords.MACRO, IPCalReservedWords.MACRO_HELP));
		proposals.put(IPCalReservedWords.DEFINE,
				getSingleProposal("define { Op1(param1, ... , paramN) == TRUE Op2(...) == TRUE }",
						IPCalReservedWords.DEFINE, IPCalReservedWords.DEFINE_HELP));
	}
	
	private static List<CompletionProposalTemplate> getSingleProposal(String replacementString, String displayString, String additionalInformation) {
		final List<CompletionProposalTemplate> proposal = new ArrayList<CompletionProposalTemplate>();
		proposal.add(new CompletionProposalTemplate(replacementString, displayString, additionalInformation));
		return proposal;
	}
}
