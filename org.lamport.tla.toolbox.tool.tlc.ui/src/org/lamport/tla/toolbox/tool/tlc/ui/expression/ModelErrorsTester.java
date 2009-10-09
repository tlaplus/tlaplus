package org.lamport.tla.toolbox.tool.tlc.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.ui.IEditorPart;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.util.UIHelper;

public class ModelErrorsTester extends PropertyTester
{

    public ModelErrorsTester()
    {
        // TODO Auto-generated constructor stub
    }

    /**
     * 
     */
    public boolean test(Object receiver, String property, Object[] args, Object expectedValue)
    {
        if (UIHelper.getActivePage() != null)
        {
            IEditorPart activeEditor = UIHelper.getActivePage().getActiveEditor();
            if (activeEditor != null)
            {
                if (activeEditor instanceof ModelEditor)
                {
                    ModelEditor activeModelEditor = (ModelEditor) activeEditor;
                    ILaunchConfiguration config = activeModelEditor.getConfig();
                    if (config != null)
                    {
                        return TLCOutputSourceRegistry.getSourceRegistry().getProvider(config).getErrors().size() > 0;
                    }
                }
            }
        }
        return false;
    }

}
