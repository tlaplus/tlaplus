package org.lamport.tla.toolbox.tool.prover.ui.dialog;

import java.net.MalformedURLException;
import java.net.URL;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.resource.JFaceColors;
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
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.browser.IWebBrowser;
import org.eclipse.ui.browser.IWorkbenchBrowserSupport;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.widgets.Hyperlink;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * This is a dialog for displaying TLAPM error messages.
 * TLAPM error messages have a message and a URL for submitting
 * that message to the TLAPM developers. This dialog will display
 * the message and display the URL as a link.
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAPMErrorDialog extends Dialog
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
     * The url of for submitting the error
     * to the TLAPM developers.
     */
    private String url;

    /**
     * Creates a new dialog that can be opened in the shell returned
     * by the given shell provider. This dialog will display the
     * given message when opened. See {@link #open()}.
     * 
     * @param parentShell
     * @param message
     */
    protected TLAPMErrorDialog(IShellProvider parentShell, String message)
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

        /*
         * The following creates the composite that will hold two widgets:
         * 
         * 1.) A label telling the user to submit the above message to
         * the given url.
         * 2.) A hyperlink widget that the user can click on to open
         * a browser to the given url.
         * 
         * We put these in a separate composite so that we can lay them out
         * with different widget columns than the outer composite. If we made the
         * hyperlink and label widgets direct children of the outer composite, then
         * they would have to be put into the columns of the outer composite which
         * can look a bit strange.
         */
        Composite linkComposite = new Composite(composite, SWT.NONE);
        GridData gd = new GridData();
        gd.horizontalSpan = 2;
        linkComposite.setLayoutData(gd);
        linkComposite.setLayout(new GridLayout(2, false));

        Label label = new Label(linkComposite, SWT.WRAP);
        label.setText("Please submit the above message to the TLAPM developers using the following link : ");
        // create the hyperlink for submitting the message
        Hyperlink link = new Hyperlink(linkComposite, SWT.WRAP);
        link.setForeground(JFaceColors.getHyperlinkText(UIHelper.getCurrentDisplay()));
        link.setUnderlined(true);
        link.setHref(url);
        link.setText(url);
        // adds a listener to the hyperlink that opens the link in
        // an external browser when it is clicked on
        link.addHyperlinkListener(new HyperlinkAdapter() {
            public void linkActivated(HyperlinkEvent e)
            {
                try
                {
                    IWorkbenchBrowserSupport browserSupport = PlatformUI.getWorkbench().getBrowserSupport();
                    IWebBrowser browser = browserSupport.getExternalBrowser();

                    browser.openURL(new URL(url));
                } catch (PartInitException e1)
                {
                    ProverUIActivator.logError("Error opening browser to url : " + url, e1);
                } catch (MalformedURLException e1)
                {
                    ProverUIActivator.logError("Malformed URL : " + url, e1);
                }
            }
        });

        return composite;
    }

    /**
     * Convenience method for opening an error dialog displaying the
     * given title and message in the currently active shell. The image
     * for this dialog will be the swt error image as returned by
     * UIHelper.getSWTImage(SWT.ICON_ERROR).
     * 
     * @param message
     */
    public static void open(String message, String title, String url)
    {
        TLAPMErrorDialog dialog = new TLAPMErrorDialog(UIHelper.getShellProvider(), message);
        dialog.setTitle(title);
        dialog.setImage(UIHelper.getSWTImage(SWT.ICON_ERROR));
        dialog.setURL(url);

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

    public void setURL(String url)
    {
        this.url = url;
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
