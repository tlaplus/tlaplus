package org.lamport.tla.toolbox.tool.tlc.launch.ui;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.debug.ui.ILaunchConfigurationTab;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.handlers.IConfigurationConstants;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelConfigurationTab extends AbstractLaunchConfigurationTab implements ILaunchConfigurationTab,
        IConfigurationConstants, IConfigurationDefaultConstants
{
    private Text rootFileText;
    private Text specNameText;
    private Text modelRootFileText;

    private Text defaultConfigFileText;
    private Text otherConfigFileText;
    private Button useDefaultConfig;
    private Button useOtherConfig;

    /* (non-Javadoc)
     * @see org.eclipse.debug.ui.ILaunchConfigurationTab#createControl(org.eclipse.swt.widgets.Composite)
     */
    public void createControl(Composite parent)
    {
        // composite
        Composite control = new Composite(parent, SWT.FILL);
        control.setLayout(new GridLayout(1, true));

        // group around specification
        createSpecificationGroup(createNewGroup(control, "Specification", 2));

        // group around model
        createConfigurationGroup(createNewGroup(control, "Configuration", 2));

        // setup the control
        setControl(control);

    }

    /**
     * @param groupParent
     */
    private void createConfigurationGroup(Composite groupParent)
    {

        // model name label
        Label modelNameLabel = new Label(groupParent, SWT.SIMPLE);
        modelNameLabel.setText("Model root file");

        // model name field
        modelRootFileText = new Text(groupParent, SWT.BORDER | SWT.SIMPLE | SWT.FILL);
        GridData gd1 = new GridData(GridData.FILL_HORIZONTAL);
        gd1.widthHint = 400;
        modelRootFileText.setLayoutData(gd1);

        // button for configuration selection
        useDefaultConfig = new Button(groupParent, SWT.RADIO);
        useDefaultConfig.setText("Default:");
        useDefaultConfig.setSelection(true);
        useDefaultConfig.addSelectionListener(new SelectionListener() {

            public void widgetDefaultSelected(SelectionEvent e)
            {
                configurationSwitched();
            }

            public void widgetSelected(SelectionEvent e)
            {
                configurationSwitched();
            }
        });

        // configuration file
        defaultConfigFileText = new Text(groupParent, SWT.BORDER | SWT.SIMPLE | SWT.FILL);
        GridData gd3 = new GridData(GridData.FILL_HORIZONTAL);
        gd3.widthHint = 400;
        defaultConfigFileText.setLayoutData(gd3);

        // button for configuration selection
        useOtherConfig = new Button(groupParent, SWT.RADIO);
        useOtherConfig.setText("Other:");
        useOtherConfig.setSelection(false);
        useOtherConfig.addSelectionListener(new SelectionListener() {

            public void widgetDefaultSelected(SelectionEvent e)
            {
                configurationSwitched();
            }

            public void widgetSelected(SelectionEvent e)
            {
                configurationSwitched();
            }
        });

        otherConfigFileText = new Text(groupParent, SWT.BORDER | SWT.SIMPLE | SWT.FILL);
        GridData gd4 = new GridData(GridData.FILL_HORIZONTAL);
        gd4.widthHint = 400;
        otherConfigFileText.setLayoutData(gd4);
        otherConfigFileText.setEnabled(false);

    }

    private void configurationSwitched()
    {
        setDirty(true);
        otherConfigFileText.setEnabled(!useOtherConfig.getSelection());
        defaultConfigFileText.setEnabled(!useDefaultConfig.getSelection());
        updateLaunchConfigurationDialog();
    }

    /**
     * @param groupParent
     */
    private void createSpecificationGroup(Composite groupParent)
    {
        // spec name label
        Label specNameLabel = new Label(groupParent, SWT.SIMPLE);
        specNameLabel.setText("Spec name");

        // spec name field
        specNameText = new Text(groupParent, SWT.BORDER | SWT.SIMPLE | SWT.FILL);
        specNameText.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, true, false));
        GridData gd1 = new GridData(GridData.FILL_HORIZONTAL);
        gd1.widthHint = 400;
        specNameText.setLayoutData(gd1);

        // root file label
        Label rootFileLabel = new Label(groupParent, SWT.SIMPLE);
        rootFileLabel.setText("Root file");

        // root file field
        rootFileText = new Text(groupParent, SWT.BORDER | SWT.SIMPLE | SWT.FILL);
        GridData gd2 = new GridData(GridData.FILL_HORIZONTAL);
        gd2.widthHint = 400;
        rootFileText.setLayoutData(gd2);

    }

    /* (non-Javadoc)
     * @see org.eclipse.debug.ui.ILaunchConfigurationTab#getName()
     */
    public String getName()
    {
        return "TLC Model Setup";
    }

    public Image getImage()
    {
        return TLCActivator.getImageDescriptor("icons/sample.gif").createImage();
    }

    /* (non-Javadoc)
     * @see org.eclipse.debug.ui.ILaunchConfigurationTab#initializeFrom(org.eclipse.debug.core.ILaunchConfiguration)
     */
    public void initializeFrom(ILaunchConfiguration configuration)
    {

        try
        {
            String specName = configuration.getAttribute(SPEC_NAME, SPEC_NAME_DEFAULT);
            String modelRootFile = configuration.getAttribute(MODEL_ROOT_FILE, MODEL_ROOT_FILE_DEFAULT);
            String specRootFile = configuration.getAttribute(SPEC_ROOT_FILE, SPEC_ROOT_FILE_DEFAULT);
            String configFile = configuration.getAttribute(CONFIG_FILE, CONFIG_FILE_DEFAULT);

            this.specNameText.setText(specName);
            this.defaultConfigFileText.setText(configFile);
            this.rootFileText.setText(specRootFile);
            this.modelRootFileText.setText(modelRootFile);

        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

    /* (non-Javadoc)
     * @see org.eclipse.debug.ui.ILaunchConfigurationTab#performApply(org.eclipse.debug.core.ILaunchConfigurationWorkingCopy)
     */
    public void performApply(ILaunchConfigurationWorkingCopy configuration)
    {
        configuration.setAttribute(SPEC_NAME, specNameText.getText());
        configuration.setAttribute(MODEL_ROOT_FILE, modelRootFileText.getText());
        configuration.setAttribute(SPEC_ROOT_FILE, rootFileText.getText());
        
        if (useDefaultConfig.getSelection())
        {
            configuration.setAttribute(CONFIG_FILE, defaultConfigFileText.getText());
        } else
        {
            configuration.setAttribute(CONFIG_FILE, otherConfigFileText.getText());
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.debug.ui.ILaunchConfigurationTab#setDefaults(org.eclipse.debug.core.ILaunchConfigurationWorkingCopy)
     */
    public void setDefaults(ILaunchConfigurationWorkingCopy configuration)
    {

    }

    public Composite createNewGroup(Composite parent, String name, int columns)
    {
        // group around specification
        Group group = new Group(parent, SWT.FILL);
        GridLayout gl = new GridLayout(columns, false);
        GridData gd = new GridData(GridData.FILL_HORIZONTAL);
        group.setLayout(gl);
        group.setLayoutData(gd);
        group.setText(name);
        return group;
    }

}
