package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * A handler which presents the user with a dialog through which to choose a spec and a model.
 */
public class CloneForeignModelHandler extends AbstractHandler implements IModelConfigurationConstants {
	public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.cloneforeign";

	private static final Comparator<Model> MODEL_SORTER = (m1, m2) -> {
		return m1.getName().compareTo(m2.getName());
	};
	
	
	public Object execute(final ExecutionEvent event) throws ExecutionException {
		final TreeMap<String, TreeSet<Model>> projectModelMap = buildMap();
		if (projectModelMap == null) {
			return null;
		}
		
		final Shell shell = PlatformUI.getWorkbench().getDisplay().getActiveShell();
		final ForeignModelPicker modelPicker = new ForeignModelPicker(shell, projectModelMap);
		
		if (modelPicker.open() == Dialog.OK) {
	        final Map<String, String> parameters = new HashMap<String, String>();
	        parameters.put(CloneModelHandlerDelegate.PARAM_FOREIGN_FULLY_QUALIFIED_MODEL_NAME,
	        			   modelPicker.getFullyQualifiedNameOfSelection());

			final ExecutionEvent cloneEvent = new ExecutionEvent(null, parameters, null, null);
			final CloneModelHandlerDelegate cloner = new CloneModelHandlerDelegate();
			cloner.execute(cloneEvent);
		}
        
		return null;
	}
	
	private TreeMap<String, TreeSet<Model>> buildMap() {
        final Spec currentSpec = ToolboxHandle.getCurrentSpec();
        if (currentSpec == null) {
        	return null;
        }
        
		final IProject specProject = currentSpec.getProject();
		final TreeMap<String, TreeSet<Model>> projectModelMap = new TreeMap<>();
		
		try {
			final IWorkspace iws = ResourcesPlugin.getWorkspace();
			final IWorkspaceRoot root = iws.getRoot();
			final IProject[] projects = root.getProjects();
			
			for (final IProject project : projects) {
				if (!specProject.equals(project)) {
					projectModelMap.put(project.getName(), new TreeSet<>(MODEL_SORTER));
				}
			}
			
			final String currentProjectName = specProject.getName();
			final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
			final ILaunchConfigurationType launchConfigurationType
					= launchManager.getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);
			final ILaunchConfiguration[] launchConfigurations
					= launchManager.getLaunchConfigurations(launchConfigurationType);
			for (final ILaunchConfiguration launchConfiguration : launchConfigurations) {
				final String projectName = launchConfiguration.getAttribute(IConfigurationConstants.SPEC_NAME, "-l!D!q_-l!D!q_-l!D!q_");
				if (!projectName.equals(currentProjectName)) {
					final TreeSet<Model> models = projectModelMap.get(projectName);
					
					if (models != null) {
						final Model model = launchConfiguration.getAdapter(Model.class);
						
						if (!model.isSnapshot()) {
							models.add(model);
						}
					} else {
						TLCUIActivator.getDefault().logError("Could not generate model map for [" + projectName + "]!");
					}
				}
			}
		} catch (final CoreException e) {
			TLCUIActivator.getDefault().logError("Building foreign model map.", e);
			
			return null;
		}
		
		return projectModelMap;
	}
	
	
	private static class ForeignModelPicker extends Dialog {
		private final TreeMap<String, TreeSet<Model>> specNameModelMap;
		
		private List specList;
		private List modelList;
		
		// oh SWT, you terrible terrible thing... after the dialog closes, all of the widgets are disposed - too bad, too late... 
		private String selectedFullyQualifiedName;
		
		private ForeignModelPicker(final Shell shell, final TreeMap<String, TreeSet<Model>> projectModelMap) {
			super(shell);
			
			specNameModelMap = projectModelMap;
		}
		
		private String getFullyQualifiedNameOfSelection() {
			return selectedFullyQualifiedName;
		}
		
	    @Override
	    protected Control createDialogArea(final Composite parent) {
	        final Composite container = (Composite) super.createDialogArea(parent);
	        
	        GridLayout gl = new GridLayout(2, false);
	        container.setLayout(gl);
	        
	        
	        final Composite leftPane = new Composite(container, SWT.NONE);
	        gl = new GridLayout(1, false);
	        gl.marginHeight = 0;
	        gl.marginWidth = 0;
	        leftPane.setLayout(gl);
	        GridData gd = new GridData();
	        gd.horizontalAlignment = SWT.FILL;
	        gd.grabExcessHorizontalSpace = true;
	        gd.verticalAlignment = SWT.FILL;
	        gd.grabExcessVerticalSpace = true;
	        leftPane.setLayoutData(gd);
	        
	        final Composite rightPane = new Composite(container, SWT.NONE);
	        gl = new GridLayout(1, false);
	        gl.marginHeight = 0;
	        gl.marginWidth = 0;
	        rightPane.setLayout(gl);
	        gd = new GridData();
	        gd.horizontalAlignment = SWT.FILL;
	        gd.grabExcessHorizontalSpace = true;
	        gd.verticalAlignment = SWT.FILL;
	        gd.grabExcessVerticalSpace = true;
	        rightPane.setLayoutData(gd);
	        
	        
	        Label l = new Label(leftPane, SWT.LEFT);
	        l.setFont(JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT));
	        l.setText("Spec:");
	        
	        specList = new List(leftPane, SWT.BORDER | SWT.SINGLE | SWT.V_SCROLL);
	        for (final String specName : specNameModelMap.keySet()) {
	        	specList.add(specName);
	        }
	        specList.addSelectionListener(new SelectionAdapter() {
	        	@Override
	        	public void widgetSelected(final SelectionEvent se) {
	    	        getButton(IDialogConstants.OK_ID).setEnabled(false);
	    	        selectedFullyQualifiedName = null;
	    	        
	        		modelList.removeAll();
	        		
	        		final TreeSet<Model> models = specNameModelMap.get(specList.getSelection()[0]);
	    	        for (final Model model : models) {
	    	        	modelList.add(model.getName());
	    	        }
	        	}
	        });
	        gd = new GridData();
	        gd.horizontalAlignment = SWT.FILL;
	        gd.grabExcessHorizontalSpace = true;
	        gd.verticalAlignment = SWT.FILL;
	        gd.grabExcessVerticalSpace = true;
	        specList.setLayoutData(gd);
	        
	        
	        l = new Label(rightPane, SWT.LEFT);
	        l.setFont(JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT));
	        l.setText("Model:");
	        
	        modelList = new List(rightPane, SWT.BORDER | SWT.SINGLE | SWT.V_SCROLL);
	        gd = new GridData();
	        gd.horizontalAlignment = SWT.FILL;
	        gd.grabExcessHorizontalSpace = true;
	        gd.verticalAlignment = SWT.FILL;
	        gd.grabExcessVerticalSpace = true;
	        modelList.setLayoutData(gd);
	        modelList.addSelectionListener(new SelectionAdapter() {
	        	@Override
	        	public void widgetSelected(final SelectionEvent se) {
	    	        getButton(IDialogConstants.OK_ID).setEnabled(true);
	    	        
	    	        selectedFullyQualifiedName
	    	        		= Model.fullyQualifiedNameFromSpecNameAndModelName(specList.getSelection()[0],
	    	        														   modelList.getSelection()[0]);
	        	}
	        });
	        
	        return container;
	    }
	    
	    @Override
		protected Control createButtonBar(final Composite parent) {
	    	final Control buttonBar = super.createButtonBar(parent);
	    	
	        getButton(IDialogConstants.OK_ID).setEnabled(false);
	    	
	    	return buttonBar;
	    }

	    @Override
	    protected Point getInitialSize() {
	        return new Point(500, 330);
	    }

	    @Override
	    protected void configureShell(final Shell shell) {
	        super.configureShell(shell);
	        shell.setText("Please choose a spec and a model");
	    }
	}
}
