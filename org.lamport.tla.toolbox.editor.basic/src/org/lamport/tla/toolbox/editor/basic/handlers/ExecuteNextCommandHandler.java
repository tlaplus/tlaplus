package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.NotEnabledException;
import org.eclipse.core.commands.NotHandledException;
import org.eclipse.core.commands.ParameterizedCommand;
import org.eclipse.core.commands.common.NotDefinedException;
import org.eclipse.jface.bindings.Binding;
import org.eclipse.jface.bindings.keys.KeySequence;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.jface.bindings.keys.SWTKeySupport;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.custom.VerifyKeyListener;
import org.eclipse.swt.events.FocusEvent;
import org.eclipse.swt.events.FocusListener;
import org.eclipse.swt.events.VerifyEvent;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.keys.IBindingService;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.UIHelper;

public class ExecuteNextCommandHandler extends AbstractHandler implements IHandler, VerifyKeyListener, FocusListener
{

    private TLAEditor editor;
    private IDocument doc ;                          // The document being edited.
    private ISelectionProvider selectionProvider ;   // 
    private TextSelection selection ;                // The current selection.
    private int offset ;                             // The current offset.
    private IRegion lineInfo ;                       // The lineInfo for the current offset.

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        editor = EditorUtil.getTLAEditorWithFocus();
        String cmd = event.getCommand().getId();
        if (editor != null)
        {
            install();
        }

        return null;
    }

    /**
     * Listens for the first key to be pressed. If it is a digit, it
     * finds the word currently containing the caret and repeats that word
     * the number of times equal to the digit pressed. If the key pressed
     * is not a digit, this does nothing to the document and
     * removes itself from subsequent key events.
     */
    public void verifyKey(VerifyEvent event)
    {
        try
        {
            // no other listeners should respond to this event
            event.doit = false;
System.out.println("Heard keystroke.");
            
            IBindingService ibindingService = (IBindingService) 
                                  UIHelper.getActivePage().getActivePart().getSite().getService(IBindingService.class) ;
            KeyStroke keyStroke = SWTKeySupport.convertAcceleratorToKeyStroke(SWTKeySupport.convertEventToUnmodifiedAccelerator(event));
            Binding binding = ibindingService.getPerfectMatch(KeySequence.getInstance(keyStroke) );
            ParameterizedCommand pcommand = binding.getParameterizedCommand();
            IHandlerService ihandlerService = (IHandlerService) 
                        UIHelper.getActivePage().getActivePart().getSite().getService(IHandlerService.class) ;
            ihandlerService.executeCommand(pcommand, null);
        } catch (ExecutionException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (NotDefinedException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (NotEnabledException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (NotHandledException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } finally
        {

            uninstall();
        }
    }

    /**
     * This should never be called. The handler
     * should only be listening if there already is focus
     * and should be removed as a listener when focus
     * is lost.
     */
    public void focusGained(FocusEvent e)
    {
        // TODO Auto-generated method stub

    }

    /**
     * Uninstalls the handler.
     */
    public void focusLost(FocusEvent e)
    {
        uninstall();
    }

    /**
     * Should be called when the handler starts listening
     * for key strokes.
     * 
     * Adds this as a key stroke listener, adds to focus listeners
     * of the underlying text widget of the editor, and sets the
     * status line.
     * 
     * This is added as a focus listener so that it can uninstall()
     * itself if focus is lost.
     */
    private void install()
    {
 System.out.println("Start install.");
        editor.getViewer().prependVerifyKeyListener(this);
        editor.getViewer().getTextWidget().addFocusListener(this);
        editor.setStatusMessage("Example command.");
        System.out.println("End install.");
   }

    /**
     * Should be called when the handler is done listening for
     * key strokes.
     * 
     * Removes itself as a key stroke listener, a focus listener, and sets
     * the status line to the empty string.
     */
    private void uninstall()
    {
System.out.println("Start uninstall");
        // do not listen to any other key strokes
        editor.getViewer().removeVerifyKeyListener(this);

        editor.getViewer().getTextWidget().removeFocusListener(this);

        editor.setStatusMessage("");
        System.out.println("End uninstall");

    }


}
