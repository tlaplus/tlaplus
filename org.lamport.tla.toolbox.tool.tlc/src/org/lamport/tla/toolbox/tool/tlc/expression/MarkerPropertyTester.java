package org.lamport.tla.toolbox.tool.tlc.expression;

import org.eclipse.core.expressions.PropertyTester;
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
                    try
                    {
                        IMarker[] foundMarkers = ((ILaunchConfiguration) receiver).getFile().findMarkers(markerId,
                                true, IResource.DEPTH_INFINITE);

                        // attribute name was not null, checking the value, if multiple markers are present,
                        // check the all of them
                        if (attributeName != null) 
                        {
                            for (int i = 0; i < foundMarkers.length; i++)
                            {
                                Object value = foundMarkers[i].getAttribute(attributeName);
                                if (!value.equals(expectedValue)) 
                                {
                                    return false;
                                }
                            }
                            return true;
                        } else 
                        {
                            // no attribute to check, just check the presence of the markers
                            
                            boolean isPresent = true;
                            if (expectedValue != null && expectedValue instanceof Boolean)
                            {
                                isPresent = ((Boolean) expectedValue).booleanValue();
                            }

                            if (isPresent)
                            {
                                return foundMarkers.length > 0;
                            } else
                            {
                                return foundMarkers.length == 0;
                            }
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
