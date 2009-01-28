package org.lamport.tla.toolbox.spec.manager;

import org.lamport.tla.toolbox.spec.Spec;

/**
 * SpecManager is responsible for handling of specifications opened by the toolbox
 * 
 * @author zambrovski
 */
public interface ISpecManager
{
    /**
     * Retrieves a list of specification names
     * 
     * @return an array of strings
     */
    public Spec[] getRecentlyOpened();

    /**
     * Adds a specification to the list Note, the SpecManagerListener will be notified about this
     * 
     * @param spec
     *            , a specification to add
     */
    public void addSpec(Spec spec);

    /**
     * Adds a SpecManagerListener to the SpecManager The SpecManager is notifying the listener if specs are added or
     * removed
     * 
     * @param listener
     *            a listener to add
     */
    public void addSpecManagerListener(SpecManagerListener listener);

    /**
     * Removes a SpecManagerListener to the SpecManager The SpecManager is notifying the listener if specs are added or
     * removed
     * 
     * @param listener
     *            a listener to remove
     */
    public void removeSpecManagerListener(SpecManagerListener listener);

    /**
     * Sets a spec that is loaded
     * 
     * @param loadedSpec
     *            a spec that is loaded, or null if no spec is loaded The spec should be stored by the spec manager
     */
    public void setSpecLoaded(Spec loadedSpec);

    /**
     * Retrieves spec loaded by the toolbox
     * 
     * @return loaded Spec or null if no spec has been loaded
     */
    public Spec getSpecLoaded();

    /**
     * Delivers a spec with given name, or null if no such spec exists<br>
     * <b>Note:</b> This method should be used to determine if a new spec with given name can be created
     * 
     * @return a reference to existing spec or null
     */
    public Spec getSpecByName(String specName);

    /**
     * Delivers a spec with given root module, or null if no such spec exists<br>
     * <b>Note:</b> This method should be used to determine if a new spec with given root module can be created
     * 
     * @return a reference to existing spec or null
     */
    public Spec getSpecByRootModule(String rootModulePath);

    /**
     * Termination of the specManager
     */
    public void terminate();

}
