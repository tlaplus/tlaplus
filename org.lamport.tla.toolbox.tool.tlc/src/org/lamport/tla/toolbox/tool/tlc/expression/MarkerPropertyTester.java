package org.lamport.tla.toolbox.tool.tlc.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;

/**
 * Test if the marker exists 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class MarkerPropertyTester extends PropertyTester
{
    /**
     * args: {markerId, attributeName}
     * expectedValue: {value of the attribute}  
     * 
     */
    public boolean test(Object receiver, String property, Object[] args, Object expectedValue)
    {
        if ("hasMarker".equals(property))
        {
            if (args.length > 0 && args[0] instanceof String)
            {
                // first attribute is the marker id
                String markerId = (String) args[0];
                String attributeName = null;
                
                if (args.length > 1 && args[1] instanceof String) 
                {
                    // second attribute is the attribute name
                    attributeName = (String) args[1];
                }
                
                if (receiver != null && receiver instanceof ILaunchConfiguration)
                {
                	// safeguard against non-existent files.
					// This might e.g. happen if another handler's changes
					// modifies the current selection before this property
					// tester is executed
                	final IFile file = ((ILaunchConfiguration) receiver).getFile();
                	if(!file.exists()) {
                		return false;
                	}
                	
                    try
                    {
						IMarker[] foundMarkers = file.findMarkers(markerId,
                                true, IResource.DEPTH_INFINITE);

                        
                        
                        // attribute name was not null, checking the value, if multiple markers are present,
                        // check the all of them
                        if (attributeName != null) 
                        {
                            // if there are markers, check the attributes
                            for (int i = 0; i < foundMarkers.length; i++)
                            {
                                Object value = foundMarkers[i].getAttribute(attributeName);
                                if (value == null || !value.equals(expectedValue)) 
                                {
                                    return false;
                                }
                            }
                            // either no markers at all (false), or all values are valid (true)
                            return foundMarkers.length > 0;
                        } else 
                        {
                            boolean result;
                            // no attribute to check, just check the presence of the markers
                            int expectedCount = -1;
                            if (expectedValue != null && expectedValue instanceof Integer)
                            {
                                expectedCount = ((Integer)expectedValue).intValue();
                            }
                            if (expectedCount == -1)
                            {
                                // just test if there are markers present
                                result = foundMarkers.length > 0;
                            } else
                            {
                                // compare with the number 
                                result = foundMarkers.length == expectedCount;
                            }
                            return result;
                        }

                    } catch (CoreException e)
                    {
                        TLCActivator.logError("Error testing markers", e);
                    }
                }
            }
        }
        return false;
    }

}
