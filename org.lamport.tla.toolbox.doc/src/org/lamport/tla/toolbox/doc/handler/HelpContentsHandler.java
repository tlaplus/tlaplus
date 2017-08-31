package org.lamport.tla.toolbox.doc.handler;

import java.lang.reflect.Field;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.help.ui.internal.views.HelpView;
import org.eclipse.help.ui.internal.views.ReusableHelpPart;
import org.eclipse.swt.custom.BusyIndicator;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

@SuppressWarnings("restriction")
public class HelpContentsHandler extends AbstractHandler implements IHandler {

	public Object execute(ExecutionEvent event) throws ExecutionException {
		BusyIndicator.showWhile(null, new Runnable() {
			public void run() {
				final IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
				try {
					final HelpView helpView = (HelpView) window.getActivePage().showView("org.eclipse.help.ui.HelpView",
							null, IWorkbenchPage.VIEW_ACTIVATE);

					final Field f = HelpView.class.getDeclaredField("reusableHelpPart");
					f.setAccessible(true);
					final ReusableHelpPart helpPart = (ReusableHelpPart) f.get(helpView);
					helpPart.showPage(ReusableHelpPart.HV_ALL_TOPICS_PAGE, true);
				} catch (final NoSuchFieldException e) {
					e.printStackTrace();
				} catch (final SecurityException e) {
					e.printStackTrace();
				} catch (final IllegalArgumentException e) {
					e.printStackTrace();
				} catch (final IllegalAccessException e) {
					e.printStackTrace();
				} catch (final PartInitException e) {
					e.printStackTrace();
				}
			}
		});
		return null;
	}
}
