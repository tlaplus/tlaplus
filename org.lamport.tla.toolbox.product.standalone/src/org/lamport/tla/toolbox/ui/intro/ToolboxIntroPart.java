/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.ui.intro;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.NotEnabledException;
import org.eclipse.core.commands.NotHandledException;
import org.eclipse.core.commands.ParameterizedCommand;
import org.eclipse.core.commands.common.NotDefinedException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ColorDescriptor;
import org.eclipse.jface.resource.FontDescriptor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.resource.LocalResourceManager;
import org.eclipse.osgi.service.datalocation.Location;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.help.IWorkbenchHelpSystem;
import org.eclipse.ui.intro.IIntroPart;
import org.eclipse.ui.part.IntroPart;
import org.lamport.tla.toolbox.StandaloneActivator;
import org.lamport.tla.toolbox.util.ZipUtil;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

public class ToolboxIntroPart extends IntroPart implements IIntroPart {

	public static final String PERSPECTIVE_ID = "org.lamport.tla.toolbox.ui.perspective.initial";

	private Composite container;

	/**
	 * @wbp.parser.entryPoint
	 */
	public void createPartControl(Composite container) {
		this.container = container;
		createControl(container);
	}

	public static void createControl(Composite container) {
		Composite outerContainer = new Composite(container, SWT.NONE);

		// The local resource manager takes care of disposing images, fonts and
		// colors when
		// the outerContainer Composite is disposed.
		final LocalResourceManager localResourceManager = new LocalResourceManager(JFaceResources.getResources(),
				outerContainer);
		Color backgroundColor = localResourceManager
				.createColor(ColorDescriptor.createFrom(new RGB(255, 255, 228)));
		outerContainer.setBackground(backgroundColor);

		/* Logo */
		outerContainer.setLayout(new GridLayout(2, false));
		final Label lblImage = new Label(outerContainer, SWT.NONE);
		lblImage.setText("Invisible text");
		final Bundle bundle = FrameworkUtil.getBundle(ToolboxIntroPart.class);
		final URL url = FileLocator.find(bundle, new Path("images/splash_small.bmp"), null);
		final ImageDescriptor logoImage = ImageDescriptor.createFromURL(url);
		lblImage.setImage(localResourceManager.createImage(logoImage));

		/* Welcome header */
		final Label lblHeader = new Label(outerContainer, SWT.WRAP);
		lblHeader.setLayoutData(new GridData(SWT.LEFT, SWT.BOTTOM, true, false, 1, 1));

		// Double its font size
		final FontDescriptor headerFontDescriptor = JFaceResources.getHeaderFontDescriptor();
		final FontData fontData = headerFontDescriptor.getFontData()[0];
		lblHeader.setFont(localResourceManager.createFont(headerFontDescriptor.setHeight(fontData.getHeight() * 2)));

		// Color value (taken from old style.css)
		lblHeader.setForeground(localResourceManager.createColor(new RGB(0, 0, 192)));
		lblHeader.setText("Welcome to the TLA\u207A Toolbox");
		lblHeader.setBackground(backgroundColor);

		/* What is next section */

		Label lblSeparator = new Label(outerContainer, SWT.NONE);
		lblSeparator.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, false, false, 2, 1));

		final StyledText styledWhatIsNext = new StyledText(outerContainer, SWT.WRAP | SWT.CENTER);
		styledWhatIsNext.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, true, false, 2, 1));
		styledWhatIsNext.setBackground(backgroundColor);
		final String whatIsnext = "There is no specification open. Click on Help if you're not sure what you should do next.";
		final int indexOfHelp = whatIsnext.indexOf("Help");
		styledWhatIsNext.setText(whatIsnext);

		StyleRange winStyle = new StyleRange();
		winStyle.underline = true;
		winStyle.underlineStyle = SWT.UNDERLINE_LINK;

		int[] winRange = { whatIsnext.indexOf("Help"), "Help".length() };
		StyleRange[] winStyles = { winStyle };
		styledWhatIsNext.setStyleRanges(winRange, winStyles);

		// link styled text to getting started guide
		styledWhatIsNext.addListener(SWT.MouseDown, new Listener() {
			public void handleEvent(Event event) {
				// Only open help if user clicked on "Help" substring of whatIsNext.
				final int offsetAtPoint = styledWhatIsNext.getOffsetAtPoint(new Point (event.x, event.y));
				if (indexOfHelp <= offsetAtPoint && offsetAtPoint <= indexOfHelp + 4) {
					IWorkbenchHelpSystem helpSystem = PlatformUI.getWorkbench().getHelpSystem();
					helpSystem.displayHelpResource("/org.lamport.tla.toolbox.doc/html/contents.html");
				}
			}
		});

		/* Getting started text */

		final StyledText styledGettingStarted = new StyledText(outerContainer, SWT.WRAP | SWT.CENTER);
		styledGettingStarted.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, true, false, 2, 1));
		styledGettingStarted.setBackground(backgroundColor);
		final String lblString = "If this is the first time you have used the Toolbox, please read the Getting Started guide.";
		styledGettingStarted.setText(lblString);

		StyleRange style = new StyleRange();
		style.underline = true;
		style.underlineStyle = SWT.UNDERLINE_LINK;

		int[] range = { lblString.indexOf("Getting Started"), "Getting Started".length() };
		StyleRange[] styles = { style };
		styledGettingStarted.setStyleRanges(range, styles);

		// link styled text to getting started guide
		styledGettingStarted.addListener(SWT.MouseDown, new Listener() {
			public void handleEvent(Event event) {
				IWorkbenchHelpSystem helpSystem = PlatformUI.getWorkbench().getHelpSystem();
				helpSystem.displayHelpResource("/org.lamport.tla.toolbox.doc/html/gettingstarted/gettingstarted.html");
			}
		});
		
		final Label verticalFillUp = new Label(outerContainer, SWT.NONE);
		verticalFillUp.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, true, 2, 1));
		verticalFillUp.setBackground(backgroundColor);


		/* Examples */

		final StyledText styledExamples = new StyledText(outerContainer, SWT.WRAP | SWT.CENTER);
		styledExamples.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, true, false, 2, 1));
		styledExamples.setBackground(backgroundColor);
		String exampleText = "Clicking on one of the buttons below imports an introductory example into the "
				+ "Toolbox.  More examples can be found in the TLA+ examples repository.\nTo run the TLC model "
				+ "checker on an example spec, open one of its models by double-clicking on it in the Spec "
				+ "Explorer on the left.";
		styledExamples.setText(exampleText);
		
		int[] exampleRange = { exampleText.indexOf("TLA+ examples repository"), "TLA+ examples repository".length() };
		styledExamples.setStyleRanges(exampleRange, styles);
		styledExamples.addListener(SWT.MouseDown, new Listener() {
			public void handleEvent(Event event) {
				try {
					PlatformUI.getWorkbench().getBrowserSupport().getExternalBrowser()
							.openURL(new URL("https://github.com/tlaplus/Examples"));
				} catch (PartInitException | MalformedURLException e) {
					StandaloneActivator.getDefault().getLog()
							.log(new Status(Status.ERROR, StandaloneActivator.PLUGIN_ID, e.getMessage(), e));
				}
			}
		});		
		
		new Label(outerContainer, SWT.NONE);
		
		Composite examples = new Composite(outerContainer, SWT.NONE);
		examples.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false, 2, 1));
		examples.setLayout(new GridLayout(7, true));
		examples.setBackground(backgroundColor);
		
		Label lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		backgroundColor = localResourceManager.createColor(ColorDescriptor.createFrom(new RGB(255, 255, 245)));
		
		// https://github.com/tlaplus/Examples/tree/master/specifications/MissionariesAndCannibals
		Button btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
		btnNewButton.setBackground(backgroundColor);
		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		btnNewButton.setAlignment(SWT.CENTER);
		btnNewButton.setText("Missionaries and Cannibals\n(TLA+)");
		btnNewButton.setData(specKey, "MissionariesAndCannibals.tla");
		btnNewButton.setData(zipKey, "examples/MissionariesAndCannibals.zip");
		btnNewButton.addSelectionListener(selectionAdapter);		
		// From https://en.wikipedia.org/wiki/Missionaries_and_cannibals_problem
		btnNewButton.setToolTipText(
				"Three missionaries and three cannibals must cross a river using a boat which can carry at most two people,"
				+ " under the constraint that, for both banks, if there are missionaries present on the bank, they "
				+ "cannot be outnumbered by cannibals (if they were, the cannibals would eat the missionaries). "
				+ "The boat cannot cross the river by itself with no people on board.");
		
		lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		// https://github.com/tlaplus/Examples/tree/master/specifications/N-Queens
		btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
		btnNewButton.setBackground(backgroundColor);
		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		btnNewButton.setAlignment(SWT.CENTER);
		btnNewButton.setText("N Queens\n(TLA+)");
		btnNewButton.setData(specKey, "Queens.tla");
		btnNewButton.setData(zipKey, "examples/Queens.zip");
		btnNewButton.addSelectionListener(selectionAdapter);		
		// Wording adopted from https://en.wikipedia.org/wiki/Eight_queens_puzzle
		btnNewButton.setToolTipText(
				"The N queens puzzle is the problem of placing N chess queens on an N×N chessboard so that no two "
				+ "queens threaten each other.");
		
		lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		// https://github.com/tlaplus/Examples/tree/master/specifications/N-Queens
		btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
		btnNewButton.setBackground(backgroundColor);
		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		btnNewButton.setAlignment(SWT.CENTER);
		btnNewButton.setData(specKey, "QueensPluscal.tla");
		btnNewButton.setData(zipKey, "examples/Queens.zip");
		btnNewButton.addSelectionListener(selectionAdapter);		
		btnNewButton.setText("N Queens\n(PlusCal)");
		// Wording adopted from https://en.wikipedia.org/wiki/Eight_queens_puzzle
		btnNewButton.setToolTipText(
				"The N queens puzzle is the problem of placing N chess queens on an N×N chessboard so that no two "
				+ "queens threaten each other.");
		
		lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		// second row
		
		lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 7, 1));
//
//		// third row
//		
//		lbl = new Label(examples, SWT.NONE);
//		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//		
//		// https://github.com/tlaplus/Examples/tree/master/specifications/Prisoners
//		btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
//		btnNewButton.setBackground(backgroundColor);
//		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//		btnNewButton.setAlignment(SWT.CENTER);
//		btnNewButton.setText("Prisoners\n(TLA+, Liveness)");
//		btnNewButton.setData(specKey, "Prisoners.tla");
//		btnNewButton.setData(zipKey, "examples/Prisoners.zip");
//		btnNewButton.addSelectionListener(selectionAdapter);		
//		btnNewButton.setToolTipText(
//				"The warden of a prison gives his prisoners the following problem. There is a room in the prison with two switches, labeled A and B. Each switch can be either up or down.  Every so often, the warden will select a prisoner at random and take him into the room, where he must flip (change the position of) exactly one of the switches. The only guarantee he makes is that every prisoner will eventually be brought into the room multiple times.  (More precisely, there will never be a time after which some prisoner is never again brought into the room.)                                          \n"
//						+ "                                                                 \n"
//						+ "At any time, any prisoner may declare that all the prisoners have been in the room at least once.  If that prisoner is right, then all the prisoners go free.  If he is wrong, all the prisoners are immediately executed.                                            \n"
//						+ "                                                                 \n"
//						+ "The prisoners are allowed to decide upon a strategy, after which they will not be allowed to communicate with one another.  And, of course, they cannot see the room or who is being brought into it. What do they do?");
//		
//		lbl = new Label(examples, SWT.NONE);
//		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//		
//		// https://github.com/tlaplus/Examples/tree/master/specifications/tower_of_hanoi
//		// Download archive via: https://minhaskamal.github.io/DownGit/#/home?url=https://github.com/tlaplus/Examples/tree/master/specifications/tower_of_hanoi&fileName=Hanoi&rootDirectory=false
//		btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
//		btnNewButton.setBackground(backgroundColor);
//		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//		btnNewButton.setAlignment(SWT.CENTER);
//		btnNewButton.setData(specKey, "Hanoi.tla");
//		btnNewButton.setData(zipKey, "examples/Hanoi.zip");
//		btnNewButton.addSelectionListener(selectionAdapter);		
//		btnNewButton.setText("Towers of Hanoi\n(TLA+)");
//		// From https://en.wikipedia.org/wiki/Tower_of_Hanoi
//		btnNewButton.setToolTipText(
//				"The Tower of Hanoi is a mathematical game or puzzle. It consists of three rods and a number of disks of different sizes, which can slide onto any rod. The puzzle starts with the disks in a neat stack in ascending order of size on one rod, the smallest at the top, thus making a conical shape.\n" + 
//				"\n" + 
//				"The objective of the puzzle is to move the entire stack to another rod, obeying the following simple rules:\n" + 
//				"\n" + 
//				" -  Only one disk can be moved at a time.\n" + 
//				" -  Each move consists of taking the upper disk from one of the stacks and placing it on top of another stack or on an empty rod.\n" + 
//				" -  No larger disk may be placed on top of a smaller disk.\n" + 
//				"\n" + 
//				"With 3 disks, the puzzle can be solved in 7 moves. The minimal number of moves required to solve a Tower of Hanoi puzzle is 2n − 1, where n is the number of disks. ");
//		
//		lbl = new Label(examples, SWT.NONE);
//		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//		
//		// https://github.com/tlaplus/Examples/tree/master/specifications/allocator
//		btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
//		btnNewButton.setBackground(backgroundColor);
//		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//		btnNewButton.setAlignment(SWT.CENTER);
//		btnNewButton.setText("Simple Allocator\n(PlusCal)");
//		btnNewButton.setData(specKey, "SimpleAllocator.tla");
//		btnNewButton.setData(zipKey, "examples/SimpleAllocator.zip");
//		btnNewButton.addSelectionListener(selectionAdapter);		
//		btnNewButton.setToolTipText(
//				"Specification of an allocator managing a set of resources:\n"
//						+ "- Clients can request sets of resources whenever all their previous requests have been satisfied.\n"
//						+ "- Requests can be partly fulfilled, and resources can be returned even before the full request has been satisfied. However, clients only have an obligation to return resources after they have obtained all resources they requested.");
//		
//		lbl = new Label(examples, SWT.NONE);
//		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
//
//		// fourth row
//		
//		lbl = new Label(examples, SWT.NONE);
//		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 7, 1));
		
		// fifth row
		
		lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		// https://github.com/tlaplus/Examples/tree/master/specifications/ewd840
		btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
		btnNewButton.setBackground(backgroundColor);
		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		btnNewButton.setAlignment(SWT.CENTER);
		btnNewButton.setText("Termination Detection\n(TLA+)");
		btnNewButton.setData(specKey, "EWD840.tla");
		btnNewButton.setData(zipKey, "examples/EWD840.zip");
		btnNewButton.addSelectionListener(selectionAdapter);		
		btnNewButton.setToolTipText(
				"A specification of Dijkstra's algorithm for termination detection in a ring. The algorithm was published as Edsger W. Dijkstra: Derivation of a termination detection algorithm for distributed computations. Inf. Proc. Letters 16:217-219 (1983).");

		lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		// https://github.com/tlaplus/Examples/tree/master/specifications/ewd840
		btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
		btnNewButton.setBackground(backgroundColor);
		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		btnNewButton.setAlignment(SWT.CENTER);
		btnNewButton.setText("Termination Detection\n(TLAPS)");
		btnNewButton.setData(specKey, "EWD840_proof.tla");
		btnNewButton.setData(zipKey, "examples/EWD840.zip");
		btnNewButton.addSelectionListener(selectionAdapter);		
		btnNewButton.setToolTipText(
				"A specification of Dijkstra's algorithm for termination detection in a ring. The algorithm was published as Edsger W. Dijkstra: Derivation of a termination detection algorithm for distributed computations. Inf. Proc. Letters 16:217-219 (1983).");
		
		lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		// https://github.com/tlaplus/Examples/tree/master/specifications/dijkstra-mutex
		btnNewButton = new Button(examples, SWT.WRAP | SWT.FLAT);
		btnNewButton.setBackground(backgroundColor);
		btnNewButton.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		btnNewButton.setAlignment(SWT.CENTER);
		btnNewButton.setText("Dijkstra Mutex\n(PlusCal)");
		btnNewButton.setData(specKey, "DijkstraMutex.tla");
		btnNewButton.setData(zipKey, "examples/DijkstraMutex.zip");
		btnNewButton.addSelectionListener(selectionAdapter);		
		btnNewButton.setToolTipText(
				"This is a PlusCal version of the first published mutual exclusion algorithm, which appeared in\n" + 
				"\n" + 
				"E. W. Dijkstra\n" + 
				"\"Solution of a Problem in Concurrent Programming Control\"  \n" + 
				"Communications of the ACM 8, 9 (September 1965) page 569");
		
		lbl = new Label(examples, SWT.NONE);
		lbl.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		// a little bit of space.
		new Label(outerContainer, SWT.NONE);
		new Label(outerContainer, SWT.NONE);
		
		/* Toolbox version */

		final Label horizontalLine = new Label(outerContainer, SWT.SEPARATOR | SWT.HORIZONTAL);
		horizontalLine.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 2, 1));

		final Label lblVersion = new Label(outerContainer, SWT.WRAP);
		lblVersion.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 2, 1));
		lblVersion.setText("Version 1.5.8 of Day Month 20??");
		lblVersion.setBackground(backgroundColor);
	}

	public void standbyStateChanged(boolean standby) {
		// do nothing for now (don't expect users to
		// send welcome to standy)
	}

	public void setFocus() {
		container.setFocus();
	}
	
	private static final String specKey = "tla-spec";
	private static final String zipKey = "tla-zip";
	
	private static SelectionAdapter selectionAdapter = new SelectionAdapter() {
		
		@Override
		public void widgetSelected(SelectionEvent se) {

			final String spec = (String) se.widget.getData(specKey);
			final String zip = (String) se.widget.getData(zipKey);

			final URL resource = StandaloneActivator.getDefault().getBundle().getResource(zip);
			final Location instanceLocation = Platform.getInstanceLocation();

			try {
				// Force-open the getting started guide that new users should read.
				final Map<String, String> params = new HashMap<>();
				params.put("org.lamport.tla.toolbox.doc.contents.param",
						"/org.lamport.tla.toolbox.doc/html/gettingstarted/gettingstarted.html");
				runCommand("org.lamport.tla.toolbox.doc.contents", params);
				
				// TODO If the zip is large, this will block the main/UI thread.
				final File destDir = ZipUtil.unzip(resource.openStream(),
						new File(instanceLocation.getURL().getFile() + File.separator + spec.replaceFirst(".tla$", "")),
						true);

				params.clear();
				params.put("toolbox.command.spec.new.param", destDir.getAbsolutePath() + File.separator + spec);
				runCommand("toolbox.command.spec.new", params);
				
			} catch (IOException ex) {
				StandaloneActivator.getDefault().logError(ex.getMessage(), ex);
			}
		}
		
		private Object runCommand(String commandId, Map<String, String> parameters) {
			// Do not rely on the UI to be up and running when trying to execute a
			// command
			IHandlerService handlerService = (IHandlerService) PlatformUI.getWorkbench().getService(IHandlerService.class);
			ICommandService commandService = (ICommandService) PlatformUI.getWorkbench().getService(ICommandService.class);

			// Guard against NPEs anyway (e.g. some asynchronous jobs might try to
			// run a
			// command after shutdown has been called on the workbench in which case
			// either service might be null
			if (handlerService == null || commandService == null) {
				StandaloneActivator.getDefault().logInfo(
						"No IHandlerService|ICommandService available while trying to execute a command");
				return null;
			}

			try {
				Command command = commandService.getCommand(commandId);
				ParameterizedCommand pCommand = ParameterizedCommand.generateCommand(command, parameters);
				return handlerService.executeCommand(pCommand, null);
			} catch (NotDefinedException e) {
				StandaloneActivator.getDefault().logError(e.getMessage(), e);
			} catch (NotEnabledException e) {
				StandaloneActivator.getDefault().logError(e.getMessage(), e);
			} catch (NotHandledException e) {
				StandaloneActivator.getDefault().logError(e.getMessage(), e);
			} catch (ExecutionException e) {
				MessageDialog.openError(Display.getCurrent().getActiveShell(), "Failed to execute.", e.getMessage());
				StandaloneActivator.getDefault().logError(e.getMessage(), e);
			}

			return null;
		}
	};
	
	/*
## tower_of_hanoi Hanoi
https://minhaskamal.github.io/DownGit/#/home?url=https://github.com/tlaplus/Examples/tree/master/specifications/tower_of_hanoi&fileName=Hanoi&rootDirectory=false

## Prisoners Prisoners.tla
https://minhaskamal.github.io/DownGit/#/home?url=https://github.com/tlaplus/Examples/tree/master/specifications/Prisoners&fileName=Prisoners&rootDirectory=false

## MissionariesAndCannibals MissionariesAndCannibals.tla
https://minhaskamal.github.io/DownGit/#/home?url=https://github.com/tlaplus/Examples/tree/master/specifications/MissionariesAndCannibals&fileName=MissionariesAndCannibals&rootDirectory=false

## N-Queens Queens.tla
## N-Queens QueensPluscal.tla
https://minhaskamal.github.io/DownGit/#/home?url=https://github.com/tlaplus/Examples/tree/master/specifications/N-Queens&fileName=Queens&rootDirectory=false

## dijkstra-mutex DijkstraMutex.tla
https://minhaskamal.github.io/DownGit/#/home?url=https://github.com/tlaplus/Examples/tree/master/specifications/dijkstra-mutex&fileName=DijkstraMutex&rootDirectory=false

## allocator SimpleAllocator.tla
https://minhaskamal.github.io/DownGit/#/home?url=https://github.com/tlaplus/Examples/tree/master/specifications/allocator&fileName=SimpleAllocator&rootDirectory=false

## ewd840 EWD840.tla EWD840_proof.tla
https://minhaskamal.github.io/DownGit/#/home?url=https://github.com/tlaplus/Examples/tree/master/specifications/ewd840&fileName=EWD840&rootDirectory=false
	 */
}
