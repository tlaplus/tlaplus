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
		templates.add(new CompletionProposalTemplate("process (ProcName \\in S) {\n     label: skip;\n}", 
				IPCalReservedWords.PROCESS, IPCalReservedWords.PROCESS_HELP));
		templates.add(new CompletionProposalTemplate("process (ProcName = Id) {\n    label: skip;\n}",
				IPCalReservedWords.PROCESS, IPCalReservedWords.PROCESS_HELP));
		proposals.put(IPCalReservedWords.PROCESS, templates);

		templates = new ArrayList<ToolboxCompletionProcessor.CompletionProposalTemplate>();
		templates.add(
				new CompletionProposalTemplate("if (TRUE) {\n   skip;\n};", "if-then", IPCalReservedWords.IFTHENELSE_HELP));
		templates.add(new CompletionProposalTemplate("if (TRUE) {\n   skip;\n} else {\n   skip;\n};", "if-then-else",
				IPCalReservedWords.IFTHENELSE_HELP));
		templates.add(new CompletionProposalTemplate("if (TRUE) {\n   skip;\n} else if (FALSE) {\n   skip;\n} else {\n   skip;\n};", "if-then-elseif",
				IPCalReservedWords.IFTHENELSE_HELP));
		proposals.put(IPCalReservedWords.IF, templates);

		proposals.put(IPCalReservedWords.VARIABLE,
				getSingleProposal("variable x = TRUE;", IPCalReservedWords.VARIABLE, IPCalReservedWords.VARIABLE_HELP));
		proposals.put(IPCalReservedWords.VARIABLES, getSingleProposal("variables x = TRUE;\n          y \\in {1,2,3};\n          z;",
				IPCalReservedWords.VARIABLES, IPCalReservedWords.VARIABLE_HELP));
		proposals.put(IPCalReservedWords.PROCEDURE,
				getSingleProposal("procedure PName (param1, ..., paramN) {\n  label: skip;\n}", IPCalReservedWords.PROCEDURE,
						IPCalReservedWords.PROCEDURE_HELP));
		proposals.put(IPCalReservedWords.CALL, getSingleProposal("call PName (expr1, ..., exprN)",
				IPCalReservedWords.CALL, IPCalReservedWords.PROCEDURE_HELP));
		proposals.put(IPCalReservedWords.WHILE, getSingleProposal("label: while (TRUE) {\n         skip;\n};",
				IPCalReservedWords.WHILE, IPCalReservedWords.WHILE_HELP));
		proposals.put(IPCalReservedWords.EITHER, getSingleProposal("either { skip; } or { skip; } or { skip; };",
				IPCalReservedWords.EITHER, IPCalReservedWords.EITHEROR_HELP));
		proposals.put(IPCalReservedWords.ASSERT,
				getSingleProposal("assert TRUE;", IPCalReservedWords.ASSERT, IPCalReservedWords.ASSERT_HELP));
		proposals.put(IPCalReservedWords.GOTO,
				getSingleProposal("goto label;", IPCalReservedWords.GOTO, IPCalReservedWords.GOTO_HELP));
		proposals.put(IPCalReservedWords.PRINT,
				getSingleProposal("print \"msg\";", IPCalReservedWords.PRINT, IPCalReservedWords.PRINT_HELP));
		proposals.put(IPCalReservedWords.WITH, getSingleProposal("with ( i \\in S ) {\n  skip;\n}",
				IPCalReservedWords.WITH, IPCalReservedWords.WITH_HELP));
		proposals.put(IPCalReservedWords.MACRO, getSingleProposal("macro P(param1, ... , paramN) {\n     skip;\n}",
				IPCalReservedWords.MACRO, IPCalReservedWords.MACRO_HELP));
		proposals.put(IPCalReservedWords.DEFINE,
				getSingleProposal("define {\n    Op1(param1, ... , paramN) == TRUE\n    Op2(...) == TRUE\n}",
						IPCalReservedWords.DEFINE, IPCalReservedWords.DEFINE_HELP));
	}
	
	private static List<CompletionProposalTemplate> getSingleProposal(String replacementString, String displayString, String additionalInformation) {
		final List<CompletionProposalTemplate> proposal = new ArrayList<CompletionProposalTemplate>();
		proposal.add(new CompletionProposalTemplate(replacementString, displayString, additionalInformation));
		return proposal;
	}
}
