package org.lamport.tla.toolbox.ui.contribution;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.menus.WorkbenchWindowControlContribution;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.AdapterFactory;

/**
 * A widget placed to the status line that shows the parse status of the root
 * module <br>
 * For additional help look at org.eclipse.ui.examples.contributions plugin
 * 
 * @author Simon Zambrovski
 * @version $Id: ParseStatusContributionItem.java 13736 2009-08-28 23:51:29Z
 *          lamport $
 */
public class ParseStatusContributionItem extends
		WorkbenchWindowControlContribution {
	// the element
	private Composite composite;
	// label to display status
	private Label statusLabel;

	public ParseStatusContributionItem() {
		super("specParseStatusState");
		Activator.getDefault().setParseStatusContribution(this);
	}

	protected Control createControl(Composite parent) {
		// If the composite is good just return it.
		if (composite != null && !composite.isDisposed()) {
			return composite;
		}

		// Create a composite to place the label in
		composite = new Composite(parent, SWT.NONE);
		// composite.setData(this);

		// Give some room around the control
		FillLayout layout = new FillLayout();
		layout.marginHeight = 2;
		layout.marginWidth = 2;
		composite.setLayout(layout);

		// Create label inside composite.
		statusLabel = new Label(composite, SWT.BORDER | SWT.CENTER);
		statusLabel.setToolTipText("Specification Parse Status");
		statusLabel.setSize(100, 20);

		// update status
		updateStatus();
		return composite;
	}

	// Updates status from the specification currently loaded in the SpecManager
	public void updateStatus() {
		if (statusLabel == null || statusLabel.isDisposed()) {
			return;
		}

		Spec spec = Activator.getSpecManager().getSpecLoaded();
		if (spec == null) {
			composite.setVisible(false);
			return;
		}
		statusLabel.setText(AdapterFactory.getStatusAsString(spec));
		statusLabel.setBackground(statusLabel.getDisplay().getSystemColor(
				AdapterFactory.getStatusAsSWTBGColor(spec)));
		statusLabel.setForeground(statusLabel.getDisplay().getSystemColor(
				AdapterFactory.getStatusAsSWTFGColor(spec)));
		statusLabel.redraw();
		composite.setVisible(true);
	}

	public void update() {
		updateStatus();
	}

	protected int computeWidth(Control control) {
		return 100;
	}

}
