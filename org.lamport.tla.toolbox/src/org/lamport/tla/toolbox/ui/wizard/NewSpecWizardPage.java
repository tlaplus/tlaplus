package org.lamport.tla.toolbox.ui.wizard;

import java.io.File;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.DialogPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
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
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A wizard page input of the specification name and the location of the root file
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class NewSpecWizardPage extends WizardPage
{
    private Text specNameText;
    private Text fileText;
    private Button importExisting;

    // the flags show if the fields has been touched
    private boolean specNameDirty = false;
    private boolean fileTextDirty = false;

    public static final String[] ACCEPTED_EXTENSIONS = { "*.tla", "*.*" };

    /**
     * Holds the path to the most recently browsed
     * directory
     */
    private String lastBrowsedDirectory;

    /**
     * @param pageName
     */
    public NewSpecWizardPage()
    {
        super("newSpecWizardPage");
        setTitle("New TLA+ Specification");
        setDescription("Creates a new TLA+ specification\nEnter a complete file name like c:\\jones\\specs\\foo.tla or click on Browse.");
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
        label.setText("&Root-module file:");

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
        new Label(container, SWT.NULL);

        new Label(container, SWT.NULL);

        importExisting = new Button(container, SWT.CHECK);
        importExisting.setText("Import existing");
        importExisting.setSelection(true);
        importExisting.setEnabled(false);

        gd = new GridData();
        gd.horizontalSpan = 2;
        importExisting.setLayoutData(gd);
        importExisting.addSelectionListener(new SelectionListener() {
            public void widgetDefaultSelected(SelectionEvent e)
            {
            }

            public void widgetSelected(SelectionEvent e)
            {
                dialogChanged();
            }
        });

        // disable the next/finish button
        setPageComplete(false);

        UIHelper.setHelp(container, "NewSpecWizard");

        // the created parent is the control we see
        setControl(container);

    }

    /**
     * 
     */
    protected void handleBrowse()
    {
        FileDialog openFileDialog = UIHelper.getFileDialog(this.fileText.getShell());

        // // platform dependent code
        // // on mac, we need a Save dialog in order to allow
        // // the user to type in a file name as well as select one
        // // on other platforms, an open dialog is sufficient
        // if (Platform.getOS().equals(Platform.OS_MACOSX))
        // {
        // // Mac
        // openFileDialog = new FileDialog(this.fileText.getShell(), SWT.SAVE);
        // } else
        // {
        // // all other operating systems
        // openFileDialog = new FileDialog(this.fileText.getShell(), SWT.OPEN);
        // }

        openFileDialog.setText("Open root file");

        /*
         * The directory to which the browse dialog should be opened is computed
         * by going through the following list in order until a directory is found.
         * 
         * 1.) Last directory in which the user opened a file by browsing
         * from this page. This is reset every time the user selects "Add New Spec...".
         * 2.) Directory of the root file of the most recently opened spec.
         * 3.) Home directory for the user.
         */
        String rootPath = lastBrowsedDirectory;
        if (rootPath == null)
        {
            if (Activator.isSpecManagerInstantiated())
            {
                Spec mostRecentlyOpenedSpec = Activator.getSpecManager().getMostRecentlyOpenedSpec();
                if (mostRecentlyOpenedSpec != null)
                {
                    rootPath = ResourceHelper.getParentDirName(mostRecentlyOpenedSpec.getRootFile());
                }
            }
        }
        if (rootPath == null)
        {
            rootPath = System.getProperty("user.home");
        }

        openFileDialog.setFilterPath(rootPath);

        openFileDialog.setFilterExtensions(ACCEPTED_EXTENSIONS);
        String selected = openFileDialog.open();
        if (selected != null)
        {
            // add .tla extension if no extension provided
            IPath path = new Path(selected);
            if (path.getFileExtension() == null)
            {
                selected = selected.concat(".").concat(ResourceHelper.TLA_EXTENSION);
            }
            this.fileText.setText(selected);
        }
    }

    /**
     * React on typing in fields
     */
    protected synchronized void dialogChanged()
    {

        String rootfilePath = null;
        // we should not validate, if nothing has been typed in
        if (fileTextDirty)
        {
            rootfilePath = getRootFilename();
            if ("".equals(rootfilePath)) // Text.getText() never return null
            {
                reportError("Root file name should be provided");
                return;
            } else if (new File(rootfilePath).isDirectory())
            {
                reportError("Root file should be a TLA file and not a directory");
                return;
            } else if (!rootfilePath.endsWith(".tla"))
            {
                reportError("Root file name should have a file-system path and extension .tla");
                return;
            } else if (!(new File(rootfilePath).isAbsolute()))
            {
                reportError("Root file name should have a file-system path");
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
            } else if(!ResourceHelper.isValidSpecName(specName)) {
            	reportError("Specification name is not valid. The Specification name '" + specName + "' is not a valid identifier");
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
            // the spec name field is empty, try to fill it from the module name
            if (fileTextDirty)
            {
                // if we got to this point, the fileText is a valid entry

                // just use the module name as a spec name
                String moduleName = ResourceHelper.getModuleNameChecked(getRootFilename(), false);

                // make sure module name does not violate valid spec name rules
                // see http://bugzilla.tlaplus.net/show_bug.cgi?id=112
                if(!ResourceHelper.isValidSpecName(moduleName)) {
                	reportError("Specification name is not valid. The Specification name '" + moduleName + "' is not a valid identifier");
                	return;
                }
                
                Spec existingSpec = Activator.getSpecManager().getSpecByName(moduleName);
                if (existingSpec != null)
                {
                    moduleName = Activator.getSpecManager().constructSpecName(moduleName, true);
                }
                specNameText.setText(moduleName);
            }
        }
        // project directory exists
        if (ResourceHelper.peekProject(getSpecName(), rootfilePath))
        {
            if (!importExisting.getSelection())
            {
                reportError("The " + getSpecName() + ".toolbox directory already exists at the provided location."
                        + "\nPlease select a different specification name or  root-module file.");
                return;
            }
            importExisting.setEnabled(true);
        } else
        {
            importExisting.setEnabled(false);
        }

        // every seems to be fine
        // if we reach this point, no errors have been detected

        // erase the previous messages
        this.setMessage(null);

        if (rootfilePath != null && !new File(rootfilePath).exists())
        {
            // allow this
            reportWarning("Root file name does not exist. A new file will be created.");
        }

        // we should not enable the next/finish if both fields are virgin
        if (!fileTextDirty || !specNameDirty)
        {
            return;
        }
        // enable the next/finish button
        this.setPageComplete(true);

        // stored so that if the user reopens browse, the dialog will open
        // to the last directory in which he selected a file
        lastBrowsedDirectory = ResourceHelper.getParentDirName(getRootFilename());

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
        this.setPageComplete(true);
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

    /**
     * Returns the user choice if the existing project files should be imported
     * @return
     */
    public boolean importExisting()
    {
        return importExisting.getSelection();
    }

}