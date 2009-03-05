package de.techjava.tla.ui.wizards;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExecutableExtension;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.actions.WorkspaceModifyDelegatingOperation;
import org.eclipse.ui.dialogs.IOverwriteQuery;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;

import de.techjava.tla.ui.UIPlugin;

/**
 * A wizard for TLA+ Projects
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLANewProjectWizard.java,v 1.1 2005/08/22 15:43:35 szambrovski Exp $
 */
public class TLANewProjectWizard 
	extends Wizard
	implements INewWizard, IExecutableExtension
{

	private TLANewProjectWizardPage[] 	pages;
	private IConfigurationElement 		configuretionElement;

	public TLANewProjectWizard() {
		super();
		setDialogSettings(UIPlugin.getDefault().getDialogSettings());
		setWindowTitle("TLA+ Project Wizard");
	}

	private void initializeDefaultPageImageDescriptor() 
	{
		if (configuretionElement != null) {
			String banner = configuretionElement.getAttribute("banner"); 
			if (banner != null) {
				ImageDescriptor desc = UIPlugin.getDefault().getImageDescriptor(banner);
				setDefaultPageImageDescriptor(desc);
			}
		}
	}

	public void addPages() 
	{
	    try 
	    {
		super.addPages();
		pages = new TLANewProjectWizardPage[1];
		pages[0] = new TLANewProjectWizardPage();
		addPage(pages[0]);
	    } catch (Exception e) 
	    {
	        e.printStackTrace();
	    }
	}

	/**
	 * @see org.eclipse.jface.wizard.IWizard#performFinish()
	 */
	public boolean performFinish() 
	{
		TLANewProjectOperation runnable =
			new TLANewProjectOperation(
				pages,
				new ImportOverwriteQuery());

		IRunnableWithProgress op =
			new WorkspaceModifyDelegatingOperation(runnable);
		try {
			getContainer().run(false, true, op);
		} catch (InvocationTargetException e) {
			handleException(e.getTargetException());
			return false;
		} catch (InterruptedException e) {
			return false;
		}
		BasicNewProjectResourceWizard.updatePerspective(configuretionElement);
		return true;
	}
	
	private void handleException(Throwable target) 
	{
		String title= "Project Creation Failed"; 
		String message="Project could not be created.";
		if (target instanceof CoreException) {
			IStatus status= ((CoreException)target).getStatus();
			ErrorDialog.openError(getShell(), title, message, status);
			//ExampleProjectsPlugin.log(status);
		} else {
			MessageDialog.openError(getShell(), title, target.getMessage());
			//ExampleProjectsPlugin.log(target);
		}
	}

	/**
	 * @see org.eclipse.core.runtime.IExecutableExtension#setInitializationData(org.eclipse.core.runtime.IConfigurationElement, java.lang.String, java.lang.Object)
	 */
	public void setInitializationData(IConfigurationElement config, String propertyName,Object data)
		throws CoreException 
	{
		configuretionElement = config;
		initializeDefaultPageImageDescriptor();
	}

	/**
	 * @see org.eclipse.ui.IWorkbenchWizard#init(org.eclipse.ui.IWorkbench, org.eclipse.jface.viewers.IStructuredSelection)
	 */
	public void init(IWorkbench workbench, IStructuredSelection selection) {

	}

	private class ImportOverwriteQuery 
		implements IOverwriteQuery 
	{
		public String queryOverwrite(String file) {
			String[] returnCodes = { YES, NO, ALL, CANCEL };
			int returnVal = openDialog(file);
			return returnVal < 0 ? CANCEL : returnCodes[returnVal];
		}

		private int openDialog(final String file) {
			final int[] result = { IDialogConstants.CANCEL_ID };
			getShell().getDisplay().syncExec(new Runnable() {
				public void run() {
					String title = "Overwite";
					String msg = "Do you want to overwrite " + file + "?";
					String[] options =
						{
							IDialogConstants.YES_LABEL,
							IDialogConstants.NO_LABEL,
							IDialogConstants.YES_TO_ALL_LABEL,
							IDialogConstants.CANCEL_LABEL };
					MessageDialog dialog =
						new MessageDialog(
							getShell(),
							title,
							null,
							msg,
							MessageDialog.QUESTION,
							options,
							0);
					result[0] = dialog.open();
				}
			});
			return result[0];
		}
	}

}

/*
 * $Log: TLANewProjectWizard.java,v $
 * Revision 1.1  2005/08/22 15:43:35  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */