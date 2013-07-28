/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import java.util.ArrayList;
import java.util.Arrays;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.widgets.Shell;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.ui.preference.EditorPreferencePage;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.StringHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.DefStepNode;
import tla2sany.semantic.InstanceNode;
import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.UseOrHideNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * @author lamport
 *
 */
public class RenumberProofHandler extends AbstractHandler implements IHandler
{
    /*
     * The following fields are actually used only in the execute method
     * and could be local to that method.  See the setFields method for
     * an explanation of why they are made fields.
     */
    private IDocument doc; // The document in the editor.
    private String text; // The document as a string.
    private ISelectionProvider selectionProvider; // 
    private TextSelection selection; // The current selection.
    private TheoremNode node; // The selected node
    private NonLeafProofNode pfNode;

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
    	
    	/*
    	 * Modified by LL in July 26 2013 to do the following:
    	 * When renumbering a step, this method should try to maintain alignments
    	 * in the statement of a proof step.  For example, if 
    	 * 
    	 *    <3>4xx. /\ A
    	 *            /\ B
    	 *            
    	 * is renumbered to <3>2, then 2 spaces should be deleted from the second line of
    	 * step to produce
    	 * 
    	 *    <3>2. /\ A
    	 *          /\ B
    	 *          
    	 * Here is the rule for doing this.  Note that column numbers are TLA+ 
    	 * column numbers, where the first column is column 1. 
    	 * 
    	 *   ls be the line number of the step number,
    	 *   l0, c0 be the line, column numbers of the start of the statement (the /\ A)
    	 *          in the example,
    	 *   l0 + n be the line number of the last end of the statement.
    	 *   oc = number of characters in the old step name.
    	 *   nc = number of characters in the new step name.
    	 *   
    	 * If the following conditions hold:
    	 * 
    	 *    /\ oc # nc
    	 *    /\ l0 = ls
    	 *    /\ n > 0
    	 *    /\ \A i \in 1..n : line l0 + i either contains nothing but
    	 *                       spaces or begins with c0-1 spaces
    	 *    
    	 * then nc-oc spaces are added to every line of lines l0+1 through l0+n , 
    	 * that contains a non-space character, where adding a negative number of spaces 
    	 * means deleting that many characters.
    	 * 
    	 * Note: The condition l0 = ls and the observation that the old step name precedes
    	 * the start of the statement implies that oc < c0, so oc-nc =< c0-1, so if
    	 * nc-oc is negative, the 4th conjunct of the condition implies that there
    	 * are nc-oc spaces at the beginning of every non-blank line in lines l0+1 through l0+n.
    	 * 
    	 * The implementation maintains an ArrayList addSpaces of IntPairs, such that
    	 * the entries are in order of increasing `one' fields and an element ip in
    	 * addSpaces means that ip.two spaces are to be added to the file at line ip.one.
    	 * (Again, adding a negative number of spaces means deletion.)
    	 * 
    	 */
    	
        // Set the fields and return if we didn't get
        // a TheoremNode.
        if (!setFields(true))
        {
            return null;
        }

        // Added by LL on 26 July 2013 
        // If the first step number is preceded by a tab, the IRegion computed
        // for pfNode begins after it should, which means the first step number
        // is not renamed (although instances of it are).  This is a particular 
        // instance of a general problem with tabs in specifications.  Any command
        // should do nothing if, like this one,  the presence of tabs could cause
        // it to incorrectly modify the spec.
 
       try {
			IRegion thmRegion = AdapterFactory.locationToRegion(doc, node.getLocation());
			if (text.substring(thmRegion.getOffset(), thmRegion.getOffset() + thmRegion.getLength()).indexOf('\t') != -1) {
				displayRenumberError("The Renumber Command does not work on a proof containing tabs.\n" +
			                         "You should not use tab characters in specifications.\n"  + 
						              "See the General section of the  Getting Started > Preferences  help page.") ;
				return null ;
			}
		} catch (BadLocationException e1) {
			// This shouldn't happen, so we don't handle it
		}

        
       // Set the preference store for getting the command's preferences
       IPreferenceStore store = Activator.getDefault().getPreferenceStore() ;

        try
        {
            Location stepLoc = null;
            LevelNode[] steps = pfNode.getSteps();

            // Set replace to the list of replacements.
            // Modified on 10 June 2010 by LL to handle non-TheoremNodes.
            ArrayList replace = new ArrayList(15);
            
            ArrayList addSpaces = new ArrayList<IntPair>(40) ;
            
        	
            int stepNumber = 1;
            for (int i = 0; i < steps.length; i++)
            {
                UniqueString uname = null;
                if (steps[i] instanceof TheoremNode)
                {
                    // check if the step has a leaf proof that uses <*>
                    // numbers, and abort if it does.
                    ProofNode stepPf = ((TheoremNode) steps[i]).getProof();
                    if ((stepPf != null) && (stepPf instanceof LeafProofNode))
                    {
                        Location leafPfLoc = stepPf.getLocation();
                        stepLoc = leafPfLoc;

                        IRegion ir = AdapterFactory.locationToRegion(doc, leafPfLoc);
                        String leafPfStr = doc.get(ir.getOffset(), ir.getLength());
                        if (leafPfStr.indexOf("<*>") > -1)
                        {
                            displayRenumberError("Cannot renumber proof that refers to <*> step numbers.");
                            return null;
                        }

                    }

                    // Get the step name.
                    uname = ((TheoremNode) steps[i]).getName();
                } else if (steps[i] instanceof DefStepNode)
                {
                    uname = ((DefStepNode) steps[i]).getStepNumber();
                } else if (steps[i] instanceof UseOrHideNode)
                {
                    uname = ((UseOrHideNode) steps[i]).getStepName();
                } else if (steps[i] instanceof InstanceNode)
                {
                    uname = ((InstanceNode) steps[i]).getStepName();
                }
                if (uname != null)
                {
                    String oldName = uname.toString();
                    
                    // Following use of the preference added by LL on 25 July 2013
                    // First set rename to true iff the preferences say that the
                    // step should be renamed.
                    String suffix = oldName.substring(oldName.indexOf('>')+1);
                    boolean rename = true ;
                	String preference = store.getString(EditorPreferencePage.RENUMBER_KEY);
                	if (preference == EditorPreferencePage.FIRST_DIGIT) {
                	    rename = Character.isDigit(suffix.charAt(0)) ;
                	}
                	else if (preference == EditorPreferencePage.SOME_DIGIT) {
                		int j = 0 ;
                		boolean dontRename = true ;
                		while (rename && (j < suffix.length())) {
                			if (Character.isDigit(suffix.charAt(j)) ) {
                				dontRename = false ;
                			}
                			j++ ;
                		}
                		rename = ! dontRename ;
                	}
                	else if (preference == EditorPreferencePage.ALL_DIGITS) {
                		int j = 0 ;
                		while (rename && (j < suffix.length())) {
                			if (! Character.isDigit(suffix.charAt(j)) ) {
                				rename = false ;
                			}
                			j++ ;
                		}
                	}
                	
					if (rename) {
						String newName = oldName.substring(0,
								oldName.indexOf('>') + 1)
								+ stepNumber;
						stepNumber++;
						replace.add(new StringReplacement(oldName, newName));
						
						// If this is a TheoremNode, add appropriate entries
						// to addSpaces if needed.
						if (steps[i] instanceof TheoremNode) {
							TheoremNode tstep = (TheoremNode) steps[i] ;
							int ncoc = newName.length() - oldName.length(); // nc - oc
							int ls = tstep.stn.getLocation().beginLine() ;
							Location thmLoc = tstep.getTheorem().stn.getLocation() ;
							int l0 = thmLoc.beginLine();
							int c0 = thmLoc.beginColumn() ;
							int n  = thmLoc.endLine() - l0;
							if ((ncoc != 0) && (l0 == ls) && (n > 0)) {
								// The first three conditions oc # nc, ... are satisfied.
								// set shouldAdd to true iff the fourth condition 
								// \A i \in 1..n : line l0 + i either... is satisfied
								// and set newAddSpaces to the elements that
								// should be added to addSpaces if it is satisfied.
								ArrayList newaddSpaces = new ArrayList<IntPair>(10) ;
								boolean shouldAdd = true ;
								int j = 1 ;
								while (shouldAdd && (j <= n)) {
									int lineOffset = doc.getLineOffset(l0 + j - 1) ;
									int lineLength = doc.getLineLength(l0 + j - 1) ;
									String line = doc.get(lineOffset, lineLength) ;
									// need to remove end-of-line characters, but
									// it can't hurt to remove ending spaces.
									line = StringHelper.trimEnd(line) ;
									lineLength = line.length() ;
									int k = 0 ;
									while (shouldAdd && k < c0-1 && k < lineLength) {
										if (line.charAt(k) != ' ') {
											shouldAdd = false ;
										}
										k++ ;
									}
									if (lineLength >= c0-1) {
										newaddSpaces.add(new IntPair(l0+j, ncoc)) ;
									}
									j++ ;
								}
								// if shouldAdd is true, append newaddSpaces to addSpaces
								if (shouldAdd) {
									for (j = 0; j < newaddSpaces.size(); j++) {
										addSpaces.add(newaddSpaces.get(j)) ;
									}
									
								}
							}
						}
						 
					}
                }
            }
            // Set replaceArray to the array of replacements, sorted in decreasing order
            // of oldString. This ensures that a replacement with oldString = s
            // appears in the list before a replacement having oldString a prefix of s.
            StringReplacement[] replaceArray = new StringReplacement[replace.size()];
            for (int i = 0; i < replaceArray.length; i++)
            {
                replaceArray[i] = (StringReplacement) replace.get(i);
            }
            Arrays.sort(replaceArray);

            // Set start/endRegion to the offsets delimiting the proof.
            IRegion pfRegion = AdapterFactory.locationToRegion(doc, pfNode.getLocation());
            int startRegion = pfRegion.getOffset();
            int endRegion = startRegion + pfRegion.getLength();

            // Set replacementOffsets to a list of IntPairs of the form <<os, rep>>
            // indicating that the replacement specified by replaceArray[rep] is to
            // be performed at offset os. They are sorted in order of increasing
            // offset.
            ArrayList replacementOffsets = new ArrayList(40);
            for (int i = 0; i < replaceArray.length; i++)
            {
                // Add to ArrayList the IntPairs for the replacements of
                // replaceArray[i].
                // searchFrom is the starting point for searching for next oldString
                // nextInsert is the next point in replacementOffsets to look
                // for a place to put the next replacement IntPair.
                int searchFrom = startRegion;
                int nextInsert = 0;
                boolean done = false;
                String oldString = replaceArray[i].oldStr;
                while (!done)
                {
                    int nextFound = text.indexOf(oldString, searchFrom);
                    if ((nextFound == -1) || !(nextFound < endRegion))
                    {
                        // No more instances of oldString.
                        done = true;
                    } else
                    {
                        // Found an instance of oldStr starting at nextFound
                        // Find the position in replacementOffsets to put the replacement.
                        while ((nextInsert < replacementOffsets.size())
                                && (((IntPair) replacementOffsets.get(nextInsert)).one < nextFound))
                        {
                            nextInsert++;
                        }
                        // We insert the replacement in replacementOffsets iff there is not already
                        // a replacement with the same offset (which must be for an old string of
                        // which the oldString is a prefix).
                        if ((nextInsert == replacementOffsets.size())
                                || (((IntPair) replacementOffsets.get(nextInsert)).one != nextFound))
                        {
                            replacementOffsets.add(nextInsert, new IntPair(nextFound, i));
                            nextInsert++;
                        }
                        searchFrom = nextFound + 1;
                    }
                }
            }

            // Do the replacements. We do them in reverse order so performing a
            // replacement doesn't change the offset of the following replacements.
            for (int i = replacementOffsets.size() - 1; i > -1; i--)
            {
                IntPair pair = (IntPair) replacementOffsets.get(i);
                StringReplacement rep = replaceArray[pair.two];
                // Turn the editor into a private field.
                // TLAEditor editor;
                // editor = EditorUtil.getTLAEditorWithFocus();
                // // gets the editor to which command applies
                // if (editor == null)
                // {
                // System.out.println("Editor is null as well as doc");
                // }
                // doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());
                // For some unknown reason, executing the following command
                // sets doc to null.
                doc.replace(pair.one, rep.oldStr.length(), rep.newStr);
            }

            // We now do the adding and removing of leading spaces indicated
            // by addSpaces.  Since we're converting from line numbers to
            // offsets each time, it doesn't matter in which order we make
            // the changes.
            for (int i = 0; i < addSpaces.size(); i++) {
            	IntPair pair = (IntPair) addSpaces.get(i) ;
            	int lineOffset = doc.getLineOffset(pair.one - 1) ;
            	if (pair.two > 0) {
            		doc.replace(lineOffset, 0, StringHelper.copyString(" ", pair.two)) ;
            	} 
            	else {
            		doc.replace(lineOffset, -pair.two, "") ;
            		
            	}
            }
                 
            // Test code to highlight region. Note method used to translate
            // a location to a region.
            // IRegion iregion = AdapterFactory.locationToRegion(doc, node.getLocation());
            // selectionProvider.setSelection(new TextSelection(iregion.getOffset(), pfRegion.getLength()));

        } catch (BadLocationException e)
        {

        }
        resetFields();
        
        // Save the module if preference set.
        if(store.getBoolean(EditorPreferencePage.SAVE_MODULE)) {
        	UIHelper.getActiveEditor().doSave(new NullProgressMonitor());
        }

        return null;
    }

    /* Disables or enables the command depending on whether the 
     * cursor is in a step that has a non-leaf proof.  
     * (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#setEnabled(java.lang.Object)
     */
    public void setEnabled(Object context)
    {
        setBaseEnabled(setFields(false));
    }

    /*
     * This method started out as code within execute to set the fields it
     * needs.  However, the checks it makes to see if it can do this are
     * exactly the same as the ones needed to see if the Renumber Proof
     * command should be enabled.  So, this code was put to dual purpose.
     * After setEnabled called the method, it then called resetFields
     * to reset them.  However, this doesn't work because it turns out 
     * that setEnabled can be called during the execution of 
     * IDocument.replace by execute.  The reallySet argument was then
     * added to allow the testing to be done without actually setting
     * the fields.  So, here's what the method does.
     * 
     * Checks if it can set the fields used by execute.  If it can't, it
     * returns false.  If it can and reallySet = true, then it sets those
     * fields.  It is called by execute with reallySet = true and by 
     * setEnabled with setFields = false.   
     */
    private boolean setFields(boolean reallySet)
    {
        // The following code copied with minor modifications from BoxedCommentHandler
        TLAEditor editor;
        editor = EditorUtil.getTLAEditorWithFocus();
        // gets the editor to which command applies
        if (editor == null)
        {
            return false;
        }
        IDocument doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        String text = doc.get();
        ISelectionProvider selectionProvider = editor.getSelectionProvider();
        TextSelection selection = (TextSelection) selectionProvider.getSelection();
        TheoremNode node = EditorUtil.getCurrentTheoremNode();
        if (node == null)
        {
            return false;
        }
        ProofNode pf = node.getProof();
        if (pf instanceof NonLeafProofNode)
        {
            pfNode = (NonLeafProofNode) pf;
        } else
        {
            return false;
        }
        if (reallySet)
        {
            this.doc = doc;
            this.text = text;
            this.selectionProvider = selectionProvider;
            this.selection = selection;
            this.node = node;
            

        }
        return true;
    }

    /*
     * Unsets the fields to save space.
     */
    private void resetFields()
    {
        doc = null;
        text = null;
        selectionProvider = null;
        selection = null;
        node = null;

    }

    void displayRenumberError(String msg)
    {
        Shell shell = UIHelper.getShellProvider().getShell();
        MessageDialog.openError(shell, "Renumbering Error", msg);
        resetFields();
        return;
    }

    /**
     * An object that contains two string fields, oldStr and newStr.
     * @author lamport
     *
     */
    private static class StringReplacement implements Comparable
    {
        String oldStr;
        String newStr;

        /**
         * The compareTo method compares the two old strings in the reverse
         * order, so sorting will sort them in inverse order.
         */
        public int compareTo(Object arg0)
        {
            return ((StringReplacement) arg0).oldStr.compareTo(this.oldStr);
        }

        StringReplacement(String o, String n)
        {
            oldStr = o;
            newStr = n;
        }

        public String toString()
        {
            return "`" + oldStr + "' -> `" + newStr + "'";
        }

    }

    private static class IntPair
    {
        int one;
        int two;

        IntPair(int o, int t)
        {
            one = o;
            two = t;
        }
    }
}
