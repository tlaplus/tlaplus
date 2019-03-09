package org.lamport.tla.toolbox.tool.tlc;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * This class really belongs in the <code>...tlc.ui</code> project, except that
 * this project has no cited dependency on that project and i'm hesitent to
 * introduce new dependencies.
 * 
 * @author loki der quaeler
 */
public class LongFormDialog extends Dialog {
	private final String m_title;
	private final String m_message;
	
	public LongFormDialog(final String title, final String message) {
		super(UIHelper.getShellProvider());
		
		setShellStyle(SWT.DIALOG_TRIM | SWT.RESIZE | SWT.APPLICATION_MODAL); 
		
		m_title = title;
		m_message = message;
	}

	@Override
    protected Control createDialogArea(final Composite parent) {
        final Composite container = (Composite)super.createDialogArea(parent);
        container.setLayout(new GridLayout(2, false));
        
        final Display d = container.getDisplay();
        // There is no cross platform clear way to get decoration fonts; get the "system" font and fudge.
        final Font f = d.getSystemFont();
        final GC gc = new GC(container.getShell());
        gc.setFont(f);
        final Point roughTitleSize = gc.textExtent(m_title);
        gc.dispose();
        
        final Label errorIcon = new Label(container, SWT.NONE);
        errorIcon.setImage(d.getSystemImage(SWT.ICON_ERROR));
        GridData gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        errorIcon.setLayoutData(gd);
        
        final Text text = new Text(container, (SWT.MULTI | SWT.BORDER | SWT.V_SCROLL | SWT.READ_ONLY));
        gd = new GridData();
        gd.heightHint = 180;
        gd.minimumWidth = Math.max(300, (int)((double)roughTitleSize.x * 1.2));
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        text.setLayoutData(gd);
        text.setText(m_message);
        
        container.pack();
        
        return container;
    }

	// Overridden so that we create only an "Ok" button as there is no state to cancel out of.
	@Override
	protected void createButtonsForButtonBar(Composite parent) {
		createButton(parent, IDialogConstants.OK_ID, IDialogConstants.OK_LABEL, true);
	}
	
    @Override
    protected void configureShell(final Shell newShell) {
        super.configureShell(newShell);
        newShell.setText(m_title);
    }
}
