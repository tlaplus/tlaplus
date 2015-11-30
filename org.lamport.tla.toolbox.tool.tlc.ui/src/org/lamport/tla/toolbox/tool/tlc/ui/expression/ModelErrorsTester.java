package org.lamport.tla.toolbox.tool.tlc.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.ui.IEditorPart;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.util.UIHelper;

public class ModelErrorsTester extends PropertyTester
{

    /**
     * 
     */
    public boolean test(Object receiver, String property, Object[] args, Object expectedValue)
    {
        if (UIHelper.getActivePage() != null)
        {
            IEditorPart activeEditor = UIHelper.getActiveEditor();
            if (activeEditor != null)
            {
                if (activeEditor instanceof ModelEditor)
                {
                    ModelEditor activeModelEditor = (ModelEditor) activeEditor;
                    Model model = activeModelEditor.getModel();
                    if (model != null)
                    {
                        return TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(model).getErrors().size() > 0;
                    }
                }
            }
        }
        return false;
    }

}
