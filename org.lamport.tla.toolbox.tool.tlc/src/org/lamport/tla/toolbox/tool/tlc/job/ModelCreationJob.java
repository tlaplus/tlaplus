package org.lamport.tla.toolbox.tool.tlc.job;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.action.Action;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.ModelWriter;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Creates the model files
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelCreationJob extends AbstractJob implements IModelConfigurationConstants, IModelConfigurationDefaults
{
    private IFile tlaFile;
    private IFile cfgFile;
    private ILaunchConfiguration config;

    public ModelCreationJob(ILaunchConfiguration config, IFile tlaFile, IFile cfgFile)
    {
        super("Creation of model files");
        this.config = config;
        this.tlaFile = tlaFile;
        this.cfgFile = cfgFile;
    }
    
    
    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.job.AbstractJob#getJobCompletedAction()
     */
    protected Action getJobCompletedAction()
    {
         return new Action()
         {
            public void run()
            {
                System.out.print("Model files created");
            }
         };
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IStatus run(IProgressMonitor monitor)
    {
        try
        {
            String tlaFilename = config.getAttribute(MODEL_ROOT_FILE, EMPTY_STRING);
            String rootModuleName = config.getAttribute(SPEC_ROOT_MODULE, EMPTY_STRING);
            
/*            // skip modifications if nothing changed
            long modelTime = config.getFile().getLocalTimeStamp();
            if ( modelTime <= this.tlaFile.getLocalTimeStamp() || modelTime <= this.cfgFile.getLocalTimeStamp() ) 
            {
                return Status.OK_STATUS;    
            }
*/            
            
            System.out.println("Model TLA file is: " + this.tlaFile.getName());
            System.out.println("Model CFG file is: " + this.cfgFile.getName());
            
            ModelWriter writer = new ModelWriter();
            
            // add extend primer
            writer.addPrimer(tlaFilename, rootModuleName);
            
            // constants list
            List constants = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_CONSTANTS,
                    new Vector()));
            
            // the advanced model values
            TypedSet modelValues = TypedSet.parseSet(config.getAttribute(MODEL_PARAMETER_MODEL_VALUES, EMPTY_STRING)); 
            
            // add constants and model values
            writer.addConstants(constants, modelValues);
            
            // new definitions
            writer.addNewDefinitions(config.getAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, EMPTY_STRING));

            // definition overrides list
            List overrides = ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_DEFINITIONS, new Vector()));
            writer.addFormulaList(ModelHelper.createOverridesContent(overrides, "def_ov"), "");
            
            // constraint
            writer.addFormulaList(ModelHelper.createSourceContent(MODEL_PARAMETER_CONSTRAINT, "constr", config),
                    "CONSTRAINT");
            // action constraint
            writer.addFormulaList(ModelHelper.createSourceContent(MODEL_PARAMETER_ACTION_CONSTRAINT, "action_constr",
                    config), "ACTION-CONSTRAINT");
            
            // the specification name-formula pair
            writer.addSpecDefinition(ModelHelper.createSpecificationContent(config));
            
            // invariants
            writer.addFormulaList(ModelHelper.createFormulaListContent(config.getAttribute(MODEL_CORRECTNESS_INVARIANTS,
                    new Vector()), "inv"), "INVARIANT");
            
            // properties
            writer.addFormulaList(ModelHelper.createFormulaListContent(config.getAttribute(MODEL_CORRECTNESS_PROPERTIES,
                    new Vector()), "prop"), "PROPERTY");

            // write down the files
            writer.writeFiles(tlaFile, cfgFile, monitor );
            return Status.OK_STATUS;
            
        } catch (CoreException e)
        {
            return Status.CANCEL_STATUS;
        }
    }

}
