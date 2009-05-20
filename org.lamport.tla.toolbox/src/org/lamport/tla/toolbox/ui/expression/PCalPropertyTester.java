package org.lamport.tla.toolbox.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;

/**
 * Tests if a module in the editor includes a PCal algorithm
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PCalPropertyTester extends PropertyTester
{
    private static QualifiedName key = new QualifiedName(Activator.PLUGIN_ID,
            IPreferenceConstants.CONTAINS_PCAL_ALGORITHM);
    private ISelectionProvider provider = UIHelper.getActiveEditorFileSelectionProvider(); 

    /**
     * Executes the property test determined by the parameter <code>property</code>. 
     * 
     * @param receiver the receiver of the property test
     * @param property the property to test
     * @param args additional arguments to evaluate the property. If no arguments
     *  are specified in the <code>test</code> expression an array of length 0
     *  is passed
     * @param expectedValue the expected value of the property. The value is either 
     *  of type <code>java.lang.String</code> or a boxed base type. If no value was
     *  specified in the <code>test</code> expressions then <code>null</code> is passed
     * 
     * @return returns <code>true<code> if the property is equal to the expected value; 
     *  otherwise <code>false</code> is returned
     */
    public boolean test(Object receiver, String property, Object[] args, Object expectedValue)
    {
        // IEditorInput input = ((IEditorPart) receiver).getEditorInput();
        if ("hasPCALAlgorithm".equals(property))
        {
            if (provider.getSelection() != null && !provider.getSelection().isEmpty())
            {
                IResource resource = (IResource) ((IStructuredSelection) provider.getSelection()).getFirstElement();
                try
                {
                    boolean result = false;
                    Boolean sessionProperty = (Boolean) resource.getSessionProperty(key);
                    result = (sessionProperty != null && sessionProperty.booleanValue());
                    System.out.println(resource.toString()+ " " + result);
                    return result;
                } catch (CoreException e)
                {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        }
        return false;
    }

}
