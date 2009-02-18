package org.lamport.tla.toolbox.util.pref;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.lamport.tla.toolbox.Activator;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResourceBasedPreferenceStore implements IPreferenceStore
{
    private IResource resource;
    private ListenerList listeners = new ListenerList();

    public ResourceBasedPreferenceStore(IResource resource)
    {
        this.resource = resource;
    }

    public boolean contains(String name)
    {
        try
        {
            return resource.getPersistentProperties().containsKey(name);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return false;
        }
    }

    public String getString(String name)
    {
        String value = null;
        try
        {
            value = resource.getPersistentProperty(new QualifiedName(Activator.PLUGIN_ID, name));
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return value;
    }
    
    public void setValue(String name, String value)
    {
        try
        {
            resource.setPersistentProperty(new QualifiedName(Activator.PLUGIN_ID, name), value);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    public boolean needsSaving()
    {
        return false;
    }

    public void putValue(String name, String value)
    {
        setValue(name, value);
    }

    public boolean getBoolean(String name)
    {
        return Boolean.parseBoolean(getString(name));
    }

    public double getDouble(String name)
    {
        return Double.parseDouble(getString(name));
    }

    public float getFloat(String name)
    {
        return Float.parseFloat(getString(name));
    }

    public int getInt(String name)
    {
        return Integer.parseInt(getString(name));
    }

    public long getLong(String name)
    {
        return Long.parseLong(getString(name));
    }

    public void setValue(String name, double value)
    {
        setValue(name, new Double(value).toString());
    }

    public void setValue(String name, float value)
    {
        setValue(name, new Float(value).toString());
    }

    public void setValue(String name, int value)
    {
        setValue(name, new Integer(value).toString());
    }

    public void setValue(String name, long value)
    {
        setValue(name, new Long(value).toString());
    }

    public void setValue(String name, boolean value)
    {
        setValue(name, new Boolean(value).toString());
    }

    public void addPropertyChangeListener(IPropertyChangeListener listener)
    {
        listeners.add(listener);
    }

    public void removePropertyChangeListener(IPropertyChangeListener listener)
    {
        listeners.remove(listener);
    }

    public void firePropertyChangeEvent(String name, Object oldValue, Object newValue)
    {

    }

    
    /* -------------------------------------------------- */
    public void setDefault(String name, double value)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public void setDefault(String name, float value)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public void setDefault(String name, int value)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public void setDefault(String name, long value)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public void setDefault(String name, String value)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public void setDefault(String name, boolean value)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    /* -------------------------------------------------- */
    public boolean getDefaultBoolean(String name)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public double getDefaultDouble(String name)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public float getDefaultFloat(String name)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public int getDefaultInt(String name)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public long getDefaultLong(String name)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    public String getDefaultString(String name)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
    /* -------------------------------------------------- */
    public void setToDefault(String name)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }

    public boolean isDefault(String name)
    {
        return false;
    }

}
