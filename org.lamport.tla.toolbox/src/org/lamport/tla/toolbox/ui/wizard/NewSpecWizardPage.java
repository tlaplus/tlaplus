package org.lamport.tla.toolbox.ui.wizard;

import java.io.File;

import org.eclipse.jface.dialogs.DialogPage;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * A wizard page input of the specification name and the location of the root file
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class NewSpecWizardPage extends WizardPage
{
    private Text                 specNameText;
    private Text                 fileText;

    // the flags show if the fields has been touched
    private boolean              specNameDirty       = false;
    private boolean              fileTextDirty       = false;

    public static final String[] ACCEPTED_EXTENSIONS = { "*.tla", "*.*" };

    /**
     * @param pageName
     */
    public NewSpecWizardPage()
    {
        super("newSpecWizardPage");
        setTitle("New TLA+ Specification");
        setDescription("Creates a new TLA+ specification\nPlease provide the specification name and the location of the file, containing the root module.");
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
     */
    public void createControl(Composite parent)
    {
        Composite container = new Composite(parent, SWT.NULL);
        GridLayout layout = new GridLayout();
        container.setLayout(layout);
        layout.numColumns = 3;
        layout.verticalSpacing = 9;

        // root file label
        Label label = new Label(container, SWT.NULL);
        label.setText("&Root file:");

        // root file text
        fileText = new Text(container, SWT.BORDER | SWT.SINGLE);
        GridData gd = new GridData(GridData.FILL_HORIZONTAL);
        fileText.setLayoutData(gd);
        fileText.addModifyListener(new ModifyListener() {
            public synchronized void modifyText(ModifyEvent e)
            {
                fileTextDirty = true;
                dialogChanged();
            }
        });

        // brows button
        Button button = new Button(container, SWT.PUSH);
        button.setText("Browse...");
        button.addSelectionListener(new SelectionAdapter() {
            public synchronized void widgetSelected(SelectionEvent e)
            {
                handleBrowse();
            }
        });

        // spec label
        label = new Label(container, SWT.NULL);
        label.setText("&Specification name:");

        // spec text
        specNameText = new Text(container, SWT.BORDER | SWT.SINGLE);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        specNameText.setLayoutData(gd);
        specNameText.addModifyListener(new ModifyListener() {
            public synchronized void modifyText(ModifyEvent e)
            {
                specNameDirty = true;
                dialogChanged();
            }
        });
        // just to align
        Label dummy = new Label(container, SWT.NULL);
        dummy.isVisible();

        // disable the next/finish button
        setPageComplete(false);
        
        // the created parent is the control we see
        setControl(container);
    }

    /**
	 * 
	 */
    protected void handleBrowse()
    {
        FileDialog openFileDialog = new FileDialog(this.fileText.getShell(), SWT.OPEN);
        openFileDialog.setText("Open root file");
        
        IDialogSettings settings = Activator.getDefault().getDialogSettings();
        String rootPath = settings.get("ROOT_FILE_NAME");
        if (rootPath == null) 
        {
            rootPath = System.getProperty("user.home");
        }
        
        openFileDialog.setFilterPath(rootPath);

        openFileDialog.setFilterExtensions(ACCEPTED_EXTENSIONS);
        String selected = openFileDialog.open();
        if (selected != null)
        {
            this.fileText.setText(selected);
        }
    }

    /**
     * React on typing in fields
     */
    protected synchronized void dialogChanged()
    {

        // we should not validate, if nothing has been typed in
        if (fileTextDirty)
        {
            String rootfilePath = getRootFilename();
            if ("".equals(rootfilePath)) // Text.getText() never return null
            {
                reportError("Root file name should be provided");
                return;
            } else if (!new File(rootfilePath).exists())
            {
                // TODO probably allow this?
                reportWarning("Root file name does not exist. A new file will be created.");
                return;
            } else if (new File(rootfilePath).isDirectory())
            {
                reportError("Root file should be a TLA file and not a directory");
                return;
            } else if (!rootfilePath.endsWith(".tla"))
            {
                reportError("Root file name should have extension .tla");
                return;
            } else
            {
                Spec existingSpec = Activator.getSpecManager().getSpecByRootModule(rootfilePath);
                if (existingSpec != null)
                {
                    reportError("The provided root file is already used in specification " + existingSpec.getName());
                    return;
                }
            }
        }

        // we should not validate, if nothing has been typed in
        if (specNameDirty)
        {
            String specName = getSpecName();
            if ("".equals(specName)) // Text.getText() never return null
            {
                reportError("Please provide a specification name");
                return;
            } else
            {

                Spec existingSpec = Activator.getSpecManager().getSpecByName(specName);
                if (existingSpec != null)
                {
                    reportError("The specification with provided name is already exists \nand uses "
                            + existingSpec.getRootFilename() + " as root module.");
                    return;
                }

            }
        } else
        {
            // the spec name field is empty
            if (fileTextDirty)
            {
                // if we got to this point, the fileText is a valid entry

                // just use the module name as a spec name
                String moduleName = ResourceHelper.getModuleNameChecked(getRootFilename(), false);

                Spec existingSpec = Activator.getSpecManager().getSpecByName(moduleName);
                if (existingSpec != null) {
                    moduleName = ResourceHelper.constructSpecName(moduleName, true);
                }
                specNameText.setText(moduleName);
            }
        }

        // every seems to be fine
        // if we reach this point, no errors have been detected

        // erase the previous messages
        this.setMessage(null);

        // we should not enable the next/finish if both fields are virgin
        if (!fileTextDirty || !specNameDirty)
        {
            return;
        }
        // enable the next/finish button
        this.setPageComplete(true);
        
        IDialogSettings settings = Activator.getDefault().getDialogSettings();
        settings.put("ROOT_FILE_NAME", getRootFilename());

    }

    /**
     * Reports an error to the user
     * 
     * @param message
     */
    private void reportError(String message)
    {
        this.setPageComplete(false);
        this.setMessage(message, DialogPage.ERROR);
    }

    /**
     * Reports a warning to the user
     * 
     * @param message
     */
    private void reportWarning(String message)
    {
        this.setPageComplete(false);
        this.setMessage(message, DialogPage.WARNING);
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.jface.wizard.WizardPage#isPageComplete()
     */
    public boolean isPageComplete()
    {
        return super.isPageComplete();
    }

    /**
     * Retrieves the specification name
     * 
     * @return the specName
     */
    public String getSpecName()
    {
        return this.specNameText.getText();
    }

    /**
     * Retrieves the path to the root file
     * 
     * @return
     */
    public String getRootFilename()
    {
        return this.fileText.getText();
    }


}