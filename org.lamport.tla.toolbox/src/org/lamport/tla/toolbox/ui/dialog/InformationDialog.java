package org.lamport.tla.toolbox.ui.dialog;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A dialog for displaying a selectable, copy-and-pastable information
 * message. The eclipse-provided information dialogs from the class
 * {@link MessageDialog} do not seem to have those features.
 * 
 * This dialog will have a single button that says OK. It will stick to
 * the top of the toolbox and will not allow you to click on other stuff
 * until you click OK.
 * 
 * The image that appears next to the message can be set using {@link #setImage(Image)}.
 * The title for the dialog can be set using {@link #setTitle(String)}.
 * 
 * There are three static convenience methods for opening dialogs:
 * 
 *  {@link #openError(String, String)}
 *  {@link #openInformation(String, String)}
 *  {@link #openWarning(String, String)}
 * 
 * @author Daniel Ricketts
 *
 */
public class InformationDialog extends Dialog
{

    /**
     * The text widget displaying the warning
     * message.
     */
    private Text dialogText;
    /**
     * The message to be displayed in the dialog.
     */
    private String message;
    /**
     * The title of the dialog.
     */
    private String title;
    /**
     * The image for the dialog.
     */
    private Image image;

    /**
     * Creates a new dialog that can be opened in the shell returned
     * by the given shell provider. This dialog will display the
     * given message when opened. See {@link #open()}.
     * 
     * @param parentShell
     * @param message
     */
    protected InformationDialog(IShellProvider parentShell, String message)
    {
        super(parentShell);
        setShellStyle(SWT.OK | SWT.APPLICATION_MODAL);
        setBlockOnOpen(true);
        this.message = message;
    }

    /**
     * This method overrides the method in {@link Dialog} in order
     * to return the {@link Composite} that contains the widgets for
     * displaying the image (if there is one) and the message text.
     */
    protected Control createDialogArea(Composite parent)
    {

        // create the composite that will contain the image and message
        // for the dialog
        Composite composite = new Composite(parent, SWT.NONE);
        composite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
        composite.setLayout(new GridLayout(2, false));

        // creates the widget displaying the image, if there is one
        if (image != null)
        {
            Label imageLabel = new Label(composite, SWT.NULL);
            image.setBackground(imageLabel.getBackground());
            imageLabel.setImage(image);
            /*
             * The following sets the alignment and spacing of the image label within
             * the dialog. It was copied from the createMessageArea method for IconAndMessageDialog.
             */
            GridDataFactory.fillDefaults().align(SWT.CENTER, SWT.BEGINNING).applyTo(imageLabel);
        }

        // creates the widget displaying the message
        dialogText = new Text(composite, SWT.MULTI | SWT.WRAP);
        dialogText.setText(message);
        dialogText.setEditable(false);
        /*
         * The following sets the alignment and spacing of the dialog text within
         * the dialog. It was copied from the createMessageArea method for IconAndMessageDialog.
         */
        GridDataFactory.fillDefaults().align(SWT.FILL, SWT.BEGINNING).grab(true, false).hint(
                convertHorizontalDLUsToPixels(IDialogConstants.MINIMUM_MESSAGE_AREA_WIDTH), SWT.DEFAULT).applyTo(
                dialogText);

        return composite;
    }

    /**
     * Convenience method for opening a warning dialog displaying the
     * given title and message in the currently active shell. The image
     * for this dialog will be the swt warning image as returned by
     * UIHelper.getSWTImage(SWT.ICON_WARNING).
     * 
     * @param message
     */
    public static void openWarning(String message, String title)
    {
        InformationDialog dialog = new InformationDialog(UIHelper.getShellProvider(), message);
        dialog.setTitle(title);
        dialog.setImage(UIHelper.getSWTImage(SWT.ICON_WARNING));

        dialog.open();
    }

    /**
     * Convenience method for opening an error dialog displaying the
     * given title and message in the currently active shell. The image
     * for this dialog will be the swt error image as returned by
     * UIHelper.getSWTImage(SWT.ICON_ERROR).
     * 
     * @param message
     */
    public static void openError(String message, String title)
    {
        InformationDialog dialog = new InformationDialog(UIHelper.getShellProvider(), message);
        dialog.setTitle(title);
        dialog.setImage(UIHelper.getSWTImage(SWT.ICON_ERROR));

        dialog.open();
    }

    /**
     * Convenience method for opening an information dialog displaying the
     * given title and message in the currently active shell. The image
     * for this dialog will be the swt information image as returned by
     * UIHelper.getSWTImage(SWT.ICON_INFORMATION).
     * 
     * @param message
     */
    public static void openInformation(String message, String title)
    {
        InformationDialog dialog = new InformationDialog(UIHelper.getShellProvider(), message);
        dialog.setTitle(title);
        dialog.setImage(UIHelper.getSWTImage(SWT.ICON_INFORMATION));

        dialog.open();
    }

    /**
     * Sets the title for the dialog.
     * 
     * @param title
     */
    public void setTitle(String title)
    {
        this.title = title;
    }

    /**
     * Sets the image that will be displayed next to the message
     * in the dialog.
     * 
     * @param image
     */
    public void setImage(Image image)
    {
        this.image = image;
    }

    /**
     * This method was mostly copied from {@link MessageDialog}. Apparently
     * this is the way to set the title for a dialog.
     */
    protected void configureShell(Shell shell)
    {
        super.configureShell(shell);
        if (title != null)
        {
            shell.setText(title);
        }
    }

}
