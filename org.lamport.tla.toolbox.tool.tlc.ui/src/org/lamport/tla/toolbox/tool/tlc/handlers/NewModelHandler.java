package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelNameValidator;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;

/**
 * Handler for creation of new models
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class NewModelHandler extends AbstractHandler implements IModelConfigurationConstants
{
    public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.new";
    public static final String PARAM_SPEC_NAME = "toolbox.tool.tlc.commands.model.new.param";
    // public static final String PARAM_SPEC_NAME = "specName";

    private String modelName = null;

    /**
     * The constructor.
     */
    public NewModelHandler()
    {
    }

    /**
     *  This method is called when the TLC Model Checker / New Model command 
     *  is executed.  The last thing it does is call the Eclipse magic that
     *  calls the appropriate methods to open the model pages.  Thus, any
     *  initial settings of values in the model is done here by setting
     *  the appropriate attributes of the model.
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        String parameter = event.getParameter(PARAM_SPEC_NAME);
        Spec spec = null;
        if (parameter != null)
        {
            spec = ToolboxHandle.getSpecByName(parameter);
        } else
        {
            spec = ToolboxHandle.getCurrentSpec();
        }
        if (spec == null)
        {
            // no spec
            System.out.println("BUG: no spec");
            return null;
        }

        // project
        IProject specProject = spec.getProject();

        // root module
        // IResource specRootModule = spec.getRootFile();

        // spec object
        SpecObj specObject = spec.getRootModule();
        if (specObject == null)
        {
            System.out.println("BUG: no specObject");
            return null;
        }

        // get the launch manager
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

        // get the launch type (model check)
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

        // retrieve a new model name for the spec
        modelName = ModelHelper.constructModelName(specProject);

        IInputValidator modelNameInputValidator = new ModelNameValidator(specProject);
        final InputDialog dialog = new InputDialog(UIHelper.getShellProvider().getShell(), "New model...",
                "Please input the name of the model to create", modelName, modelNameInputValidator);

        dialog.setBlockOnOpen(true);
        UIHelper.runUISync(new Runnable() {

            public void run()
            {
                int open = dialog.open();
                switch (open) {
                case Window.OK:
                    modelName = dialog.getValue();
                    break;
                case Window.CANCEL:
                    // cancel model creation
                    modelName = null;
                }
            }
        });
        if (modelName == null)
        {
            // exit processing if no model name at place
            return null;
        }

        // get the root module
        ModuleNode moduleNode = specObject.getExternalModuleTable().getRootModule();

        // get the list of constants
        List constants = ModelHelper.createConstantsList(moduleNode);

        // if defaultInitValue is a constant, initialize it
        // to be a model value. (Should perhaps be changed to do this
        // only if the root module or some extended module has an algorithm?)
        Iterator iter = constants.iterator();
        boolean done = false;
        while ((!done) && iter.hasNext())
        {
            Assignment assign = (Assignment) iter.next();
            if (assign.getLabel().equals("defaultInitValue") && (assign.getParams().length == 0))
            {
                assign.setRight("defaultInitValue");
                done = true;
            }
        }

        try
        {
            // create new launch instance
            ILaunchConfigurationWorkingCopy launchCopy = launchConfigurationType.newInstance(specProject, specProject
                    .getName()
                    + "___" + modelName);

            launchCopy.setAttribute(SPEC_NAME, spec.getName());
            // it is easier to do launchCopy.getProject().getPersistentProperty(SPEC_ROOT_FILE)
            // launchCopy.setAttribute(SPEC_ROOT_FILE, specRootModule.getLocation().toOSString());
            launchCopy.setAttribute(MODEL_NAME, modelName);

            if (constants.size() == 0)
            {
                launchCopy.setAttribute(MODEL_PARAMETER_CONSTANTS, (List) null);
            } else
            {
                launchCopy.setAttribute(MODEL_PARAMETER_CONSTANTS, ModelHelper.serializeAssignmentList(constants));
            }

            // Initialize the Specification field of the model to be the
            // temporal formula Spec if Spec is defined by the current
            // specification to be a temporal formula. Otherwise, initialize
            // that field to be a specification with initial predicate field
            // Init and next-state action Next if those names are defined to
            // be operators of the appropriate level.
            //
            // Also, if Spec is found and Termination is defined to be a
            // temporal formula, then add it to the list of temporal properties,
            // except not checked. It is checked iff the root file
            // contains a PlusCal spec and the termination option has been
            // selected in the PlusCal options statement within the root file.
            // (It should probably also be set if the -termination option is
            // set in the preferences, but few users will set that preference.)
            OpDefNode[] defs = moduleNode.getOpDefs();
            boolean foundSpec = false;
            boolean foundInit = false;
            boolean foundNext = false;
            boolean foundTermination = false;
            // Following added by LL on 23 Jan 2011. If true, it sets
            // checking of termination detection true if fountTermination = true.
            boolean checkTermination = false;
            for (int i = 0; i < defs.length; i++)
            {
                if (defs[i].getNumberOfArgs() == 0)
                {
                    // Only look at operators with no arguments.
                    if (defs[i].getName().toString().equals("Spec") && (defs[i].getLevel() == LevelNode.TemporalLevel))
                    {
                        foundSpec = true;

                    } else if (defs[i].getName().toString().equals("Init")
                            && (defs[i].getLevel() == LevelNode.VariableLevel))
                    {
                        foundInit = true;
                    } else if (defs[i].getName().toString().equals("Next")
                            && (defs[i].getLevel() == LevelNode.ActionLevel))
                    {
                        foundNext = true;

                    } else if (defs[i].getName().toString().equals("Termination")
                            && (defs[i].getLevel() == LevelNode.TemporalLevel))
                    {
                        foundTermination = true;

                        // The following code added by LL on 23 Jan 2011
                        // to set checkTermination true iff the root module
                        // contains "PlusCal options ( ... termination "
                        // I don't really understand it, but I copied it from
                        // the code in PCalPropertyTester that searches for
                        // "--algorithm" in a module to determine if the module
                        // has a PlusCal algorithm
                        IFile ifile = spec.getRootFile();
                        FileEditorInput fileEditorInput = new FileEditorInput(ifile);
                        FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
                        try
                        {
                            fileDocumentProvider.connect(fileEditorInput);
                            IDocument document = fileDocumentProvider.getDocument(fileEditorInput);
                            FindReplaceDocumentAdapter searchAdapter = new FindReplaceDocumentAdapter(document);
                            IRegion matchRegionx = searchAdapter.find(0,
                                    "PlusCal[\\s]*options[\\s]*\\([^\\)]*termination", true, true, false, true);
                            if (matchRegionx != null)
                            {
                                checkTermination = true;
                                Activator.logDebug("Set checkTermination true for " + ifile.getName());
                            } else {
                                // search for "termination" option in properties added by LL
                                // on 24 Jan 2011.  This code was copied with little understanding from
                                // the constructor of the TranslatorJob class.
                                IPreferenceStore projectPreferenceStore = PreferenceStoreHelper.getProjectPreferenceStore(ifile
                                        .getProject());
                                String paramString = projectPreferenceStore.getString(IPreferenceConstants.PCAL_CAL_PARAMS);
                                checkTermination = (paramString.indexOf("-termination") != -1);
System.out.println("checkTermination = " + checkTermination);                               
                            }
                        } catch (CoreException e)
                        {
                            // I have no idea what can cause this exception, but if an
                            // exception occurs, we just don't set checkTermination true.
                        } catch (BadLocationException e)
                        {
                            // I have no idea what can cause this exception, but if an
                            // exception occurs, we just don't set checkTermination true.
                        } finally
                        {
                            /*
                             * The code I copied this from says:
                             * 
                             * The document provider is not needed. Always disconnect it to avoid a memory leak.
                             * 
                             * Keeping it connected only seems to provide synchronization of
                             * the document with file changes. That is not necessary in this context.
                             */
                            fileDocumentProvider.disconnect(fileEditorInput);
                        }
                        // end code added by LL on 23 Jan 2011

                    }
                }
            }
            if (foundSpec)
            {
                launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_CLOSED_SPECIFICATION, "Spec");
                launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_SPEC_TYPE,
                        IModelConfigurationDefaults.MODEL_BEHAVIOR_TYPE_SPEC_CLOSED);
                if (foundTermination)
                {
                    Vector vec = new Vector();
                    launchCopy.setAttribute(MODEL_PROPERTIES_EXPAND, "set");
                    vec.add((checkTermination ? "1" : "0") + "Termination");
                    // The first character should be 1 or 0 depending
                    // on whether or not the box enabling the property should be checked.
                    launchCopy.setAttribute(IModelConfigurationConstants.MODEL_CORRECTNESS_PROPERTIES, vec);
                }
            } else if (foundInit || foundNext)
            {
                launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_SPEC_TYPE,
                        IModelConfigurationDefaults.MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT);
                if (foundInit)
                {
                    launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT,
                            "Init");
                }
                if (foundNext)
                {
                    launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT,
                            "Next");
                }
            }
            // The following code added by LL on 9 Apr 2011 as a beginning of adding 
            // overriding for  constant definitions of the form 
            //
            //    Foo == CHOOSE v : v \notin exp
            // 
            // It was dropped pending a solution to the TLC bug with overriding definitions
            // in instantiated modules (which it led me to discover).
            // 
//            Vector overrides = new Vector();
//            for (int i = 0; i < defs.length; i++) {
//                OpDefNode node = defs[i];
//             // Replace this by a real test:
//                String defName = node.getName().toString();
//                if (defName.indexOf("Foo") != -1)
//                {
//                    overrides.addElement(defName + ";;" + defName + ";1;0");
//                }
//                if (overrides.size() != 0) {
//                    launchCopy.setAttribute(MODEL_PARAMETER_DEFINITIONS, overrides);
//                }
//            }

            ILaunchConfiguration launchSaved = launchCopy.doSave();

            // create parameters for the handler
            HashMap parameters = new HashMap();
            parameters.put(OpenModelHandler.PARAM_MODEL_NAME, modelName);

            // runs the command and opens the module [should be model?] in the editor
            //
            // Attempted explanation by LL:
            // It appears that through some multiple levels of Eclipse-induced
            // indirection, this causes the ModelEditor.openPages() method to
            // be called, which is what actually creates the model pages and
            // puts them on the screen. See the commands for UIHelper.runCommand.
            //
            UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);

            return launchSaved;

        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error creating a model", e);
        }

        return null;
    }

}
