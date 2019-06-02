package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.advanced;

import java.io.Closeable;
import java.io.IOException;
import java.util.Calendar;
import java.util.concurrent.atomic.AtomicBoolean;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Scale;
import org.eclipse.swt.widgets.Spinner;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.TLCConsumptionProfile;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.TLCPreferenceInitializer;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.util.HelpButton;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tlc2.TLCGlobals;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiFPSet;
import tlc2.util.FP64;
import util.TLCRuntime;

public class AdvancedTLCOptionsPage extends BasicFormPage implements Closeable {
    public static final String ID = "AdvancedTLCOptionsPage";
    
    private static final String TITLE = "Advanced TLC Options";
    
    
    private Spinner workers;
    private Scale maxHeapSize;
    private Label maxHeapSizeFraction;
    private AtomicBoolean programmaticallySettingWorkerParameters;

    private SourceViewer m_viewSource;

    private Button m_depthFirstOptionCheckbox;
    private Button m_modelCheckModeOption;
    private Button m_simulationModeOption;
    private Button m_deferLivenessCheckbox;
    private Button m_visualizeStateGraphCheckbox;
    private Text m_depthText;
    private Text m_simulationDepthText;
    private Text m_simulationSeedText;
    private Text m_simulationArilText;
    
    // The widgets to display the checkpoint size and the delete button.
    private Button m_checkpointRecoverCheckbox;
    private Text m_checkpointIdText;
    private Label m_checkpointSizeLabel;
    private Text m_checkpointSizeText;
    private Button m_checkpointDeleteButton;
    
    // Widgets to enable/disable coverage
    private Button m_collectCoverageCheckbox;
    
    /**
     * Offset for the -fp parameter passed to TLC process to select the hash seed 
     */
    private Spinner m_fingerprintSeedIndex;
    private Button m_randomFingerprintCheckbox;
	/**
	 * -fpbits parameter designed to select how many fp bits are used for hash
	 * lookup
	 */
    private Spinner m_fingerprintBits;
    /**
     * -maxSetSize input to set the upper bound of the TLA set
     * @see Bug #264 in general/bugzilla/index.html
     */
    private Spinner m_maxSetSize;
    /**
	 * Text box to pass additional/extra JVM arguments/system properties to
	 * nested TLC java process.
	 */
    private Text m_extraVMArgumentsText;
    /**
	 * Text box to pass additional/extra parameters to nested process.
	 */
    private Text m_extraTLCParametersText;

	/**
	 * Used to interpolate y-values for memory scale
	 */
	private final Interpolator linearInterpolator;
	
	private MainModelPage mainModelPage;

    public AdvancedTLCOptionsPage(final FormEditor editor) {
        super(editor, ID, TITLE, "icons/full/advanced_tlc_options_" + IMAGE_TEMPLATE_TOKEN + ".png");
        
        helpId = IHelpConstants.ADVANCED_TLC_OPTIONS_PAGE;

		// available system memory
		final long phySysMem = TLCRuntime.getInstance().getAbsolutePhysicalSystemMemory(1.0d);
		
		// 0.) Create LinearInterpolator with two additional points 0,0 and 1,0 which
		int s = 0;
		double[] x = new double[6];
		double[] y = new double[x.length];
		
		// base point
		y[s] = 0d;
		x[s++] = 0d;

		// 1.) Minumum TLC requirements 
		// Use hard-coded minfpmemsize value * 4 * 10 regardless of how big the
		// model is. *4 because .25 mem is used for FPs
		double lowerLimit = ( (TLCRuntime.MinFpMemSize / 1024 / 1024 * 4d) / phySysMem) / 2;
		x[s] = lowerLimit;
		y[s++] = 0d;
		
		// a.)
		// Current bloat in software is assumed to grow according to Moore's law => 
		// 2^((Year-1993)/ 2)+2)
		// (1993 as base results from a statistic of windows OS memory requirements)
		final int currentYear = Calendar.getInstance().get(Calendar.YEAR);
		double estimateSoftwareBloatInMBytes = Math.pow(2, ((currentYear - 1993) / 3) + 3.5);
		
		// 2.) Optimal range 
		x[s] = lowerLimit * 2d;
		y[s++] = 1.0d;
		x[s] = 1.0d - (estimateSoftwareBloatInMBytes / phySysMem);
		y[s++] = 1.0d;
		
		// 3.) Calculate OS reserve
		double upperLimit = 1.0d - (estimateSoftwareBloatInMBytes / phySysMem) / 2;
		x[s] = upperLimit;
		y[s++] = 0d;
		
		// base point
		x[s] = 1d;
		y[s] = 0d;
		
		linearInterpolator = new Interpolator(x, y);
        
		programmaticallySettingWorkerParameters = new AtomicBoolean(false);
    }
    
    /**
     * On a refresh, the checkpoint information is re-read 
     */
    @Override
	public void refresh() {
		super.refresh();
		updateCheckpoints();
	}
    
	@Override
	protected void createBodyContent(final IManagedForm managedForm) {
        final DataBindingManager dm = getDataBindingManager();
        final FormToolkit toolkit = managedForm.getToolkit();
        final Composite formBody = managedForm.getForm().getBody();

        GridLayout gl;
        GridData gd;

        mainModelPage = (MainModelPage)getEditor().findPage(MainModelPage.ID);
        programmaticallySettingWorkerParameters.set(true);

        final Section section = FormHelper.createSectionComposite(formBody, "TLC Configuration", "",
                toolkit, (Section.TITLE_BAR | Section.TREE_NODE | Section.EXPANDED), getExpansionListener());
        final ValidateableSectionPart launchPart = new ValidateableSectionPart(section, this, SEC_LAUNCHING_SETUP);
        managedForm.addPart(launchPart);
        final DirtyMarkingListener launchListener = new DirtyMarkingListener(launchPart, true);
        final Composite body = (Composite) section.getClient();
        gl = new GridLayout(2, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        body.setLayout(gl);
        
        /*
         * Workers Spinner
         */
        
        // label workers
        toolkit.createLabel(body, "Number of worker threads:");

        // field workers
        workers = new Spinner(body, SWT.NONE);
        workers.addSelectionListener(launchListener);
        workers.addFocusListener(focusListener);
        workers.addListener(SWT.Verify, (e) -> {
			if (!programmaticallySettingWorkerParameters.get()) {
				mainModelPage.setWorkerCount(workers.getSelection());
			}
        });
        gd = new GridData();
        gd.horizontalIndent = 40;
        gd.widthHint = 40;
        workers.setLayoutData(gd);
        
        workers.setMinimum(1);
        workers.setPageIncrement(1);
        workers.setToolTipText("Determines how many threads will be spawned working on the next state relation.");
        workers.setSelection(TLCConsumptionProfile.LOCAL_NORMAL.getWorkerThreads());
        workers.setEnabled(false);

        dm.bindAttribute(LAUNCH_NUMBER_OF_WORKERS, workers, launchPart);
        
        /*
         * MapHeap Scale
         */
        
        // max heap size label
        toolkit.createLabel(body, "Fraction of physical memory allocated to TLC:");

		// Create a composite inside the right "cell" of the "how to run"
		// section grid layout to fit the scale and the maxHeapSizeFraction
		// label into a single row.
        final Composite maxHeapScale = new Composite(body, SWT.NONE);
        gl = new GridLayout(2, false);
        maxHeapScale.setLayout(gl);
        gd = new GridData();
        gd.horizontalIndent = 30;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        maxHeapScale.setLayoutData(gd);

        // field max heap size
        int defaultMaxHeapSize = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
        maxHeapSize = new Scale(maxHeapScale, SWT.NONE);
        maxHeapSize.addSelectionListener(launchListener);
        maxHeapSize.addFocusListener(focusListener);
        maxHeapSize.addListener(SWT.Selection, (e) -> {
			if (!programmaticallySettingWorkerParameters.get()) {
				mainModelPage.setHeapPercentage(maxHeapSize.getSelection());
			}
        });
        gd = new GridData();
        gd.minimumWidth = 250;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        maxHeapSize.setLayoutData(gd);
        maxHeapSize.setMaximum(99);
        maxHeapSize.setMinimum(1);
        maxHeapSize.setPageIncrement(5);
        maxHeapSize.setSelection(defaultMaxHeapSize);
        maxHeapSize.setToolTipText("Specifies the heap size of the Java VM that runs TLC.");

        dm.bindAttribute(LAUNCH_MAX_HEAP_SIZE, maxHeapSize, launchPart);
        
        // label next to the scale showing the current fraction selected
		final TLCRuntime instance = TLCRuntime.getInstance();
		final long memory = instance.getAbsolutePhysicalSystemMemory(defaultMaxHeapSize / 100d);
		maxHeapSizeFraction = toolkit.createLabel(maxHeapScale,
				MainModelPage.generateMemoryDisplayText(defaultMaxHeapSize, memory));
		maxHeapSize.addPaintListener((pe) -> {
			maxHeapSizeFraction.setText(generateMemoryDisplayText());
			maxHeapScale.layout();
		});
        maxHeapSize.setEnabled(false);
		

        // add horizontal divider that makes the separation clear
        Label hr = toolkit.createSeparator(body, SWT.HORIZONTAL);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalSpan = 2;
        gd.verticalIndent = 6;
        hr.setLayoutData(gd);

        
        // Model checking mode
        m_modelCheckModeOption = toolkit.createButton(body, "Model-checking mode", SWT.RADIO);
        gd = new GridData();
        gd.horizontalSpan = 2;
        m_modelCheckModeOption.setLayoutData(gd);
        m_modelCheckModeOption.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				updateEnabledStatesForAdvancedLaunchRadioSelection();
			}
		});

        // label view
        final Label viewLabel = toolkit.createLabel(body, "View:");
        gd = new GridData();
        gd.verticalAlignment = SWT.BEGINNING;
        gd.horizontalIndent = 10;
        viewLabel.setLayoutData(gd);
        // field view
        m_viewSource = FormHelper.createFormsSourceViewer(toolkit, body, SWT.V_SCROLL);
        // layout of the source viewer
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.heightHint = 60;
        gd.minimumWidth = 200;
        m_viewSource.getTextWidget().setLayoutData(gd);
        m_viewSource.getTextWidget().setData(DataBindingManager.WIDGET_HAS_ENABLED_STATE_HANDLED_ELSEWHERE, new Object());

        m_depthFirstOptionCheckbox = toolkit.createButton(body, "Depth-first", SWT.CHECK);
        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.horizontalIndent = 10;
        m_depthFirstOptionCheckbox.setLayoutData(gd);
        m_depthFirstOptionCheckbox.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				m_depthText.setEnabled(m_depthFirstOptionCheckbox.getSelection());
			}
		});
        m_depthFirstOptionCheckbox.setData(DataBindingManager.WIDGET_HAS_ENABLED_STATE_HANDLED_ELSEWHERE, new Object());

        // label depth
        Label dfidDepthLabel = toolkit.createLabel(body, "Depth:");
        gd = new GridData();
        gd.horizontalIndent = 36;
        dfidDepthLabel.setLayoutData(gd);
        // field depth
        m_depthText = toolkit.createText(body, "100");
        gd = new GridData();
        gd.minimumWidth = 100;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_depthText.setLayoutData(gd);
        m_depthText.addFocusListener(focusListener);
        m_depthText.setEnabled(false);
        m_depthText.setData(DataBindingManager.WIDGET_HAS_ENABLED_STATE_HANDLED_ELSEWHERE, new Object());

        m_simulationModeOption = toolkit.createButton(body, "Simulation mode", SWT.RADIO);
        gd = new GridData();
        gd.horizontalSpan = 2;
        m_simulationModeOption.setLayoutData(gd);
        m_simulationModeOption.addFocusListener(focusListener);
        m_simulationModeOption.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				updateEnabledStatesForAdvancedLaunchRadioSelection();
			}
		});

        // label depth
        final Label depthLabel = toolkit.createLabel(body, "Maximum length of the trace:");
        gd = new GridData();
        gd.horizontalIndent = 10;
        depthLabel.setLayoutData(gd);
        // field depth
        m_simulationDepthText = toolkit.createText(body, "100");
        gd = new GridData();
        gd.minimumWidth = 100;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_simulationDepthText.setLayoutData(gd);
        m_simulationDepthText.addFocusListener(focusListener);
        m_simulationDepthText.setData(DataBindingManager.WIDGET_HAS_ENABLED_STATE_HANDLED_ELSEWHERE, new Object());

        // label seed
        final Label seedLabel = toolkit.createLabel(body, "Seed:");
        gd = new GridData();
        gd.horizontalIndent = 10;
        seedLabel.setLayoutData(gd);

        // field seed
        m_simulationSeedText = toolkit.createText(body, "");
        gd = new GridData();
        gd.minimumWidth = 200;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_simulationSeedText.setLayoutData(gd);
        m_simulationSeedText.addFocusListener(focusListener);
        m_simulationSeedText.setData(DataBindingManager.WIDGET_HAS_ENABLED_STATE_HANDLED_ELSEWHERE, new Object());

        // label seed
        final Label arilLabel = toolkit.createLabel(body, "Aril:");
        gd = new GridData();
        gd.horizontalIndent = 10;
        arilLabel.setLayoutData(gd);

        // field seed
        m_simulationArilText = toolkit.createText(body, "");
        gd = new GridData();
        gd.minimumWidth = 200;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_simulationArilText.setLayoutData(gd);
        m_simulationArilText.addFocusListener(focusListener);
        m_simulationArilText.setData(DataBindingManager.WIDGET_HAS_ENABLED_STATE_HANDLED_ELSEWHERE, new Object());

        // add horizontal divider that makes the separation clear
        hr = toolkit.createSeparator(body, SWT.HORIZONTAL);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalSpan = 2;
        gd.verticalIndent = 6;
        hr.setLayoutData(gd);

        /*
         * run from the checkpoint.  Checkpoint help button added by LL on 17 Jan 2013
         */
        Composite checkpointComposite = new Composite(body, SWT.NONE) ;
        gl = new GridLayout(2, false);
        gl.marginWidth = 0;
        gl.marginHeight = 0;
        checkpointComposite.setLayout(gl);

        gd = new GridData();
        gd.horizontalSpan = 2;
        gd.verticalIndent = 6;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalAlignment = SWT.FILL;
        checkpointComposite.setLayoutData(gd);

        m_checkpointRecoverCheckbox = toolkit.createButton(checkpointComposite, "Recover from checkpoint", SWT.CHECK);
        m_checkpointRecoverCheckbox.addFocusListener(focusListener);
        gd = new GridData();
        gd.horizontalAlignment = SWT.BEGINNING;
        m_checkpointRecoverCheckbox.setLayoutData(gd);
        
        final Button b = HelpButton.helpButton(checkpointComposite, "model/overview-page.html#checkpoint") ;
        gd = new GridData();
        gd.horizontalAlignment = SWT.END;
        gd.grabExcessHorizontalSpace = true;
        b.setLayoutData(gd);

        toolkit.createLabel(body, "Checkpoint ID:");

        m_checkpointIdText = toolkit.createText(body, "");
        m_checkpointIdText.setEditable(false);
        gd = new GridData();
        gd.minimumWidth = 100;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_checkpointIdText.setLayoutData(gd);

        m_checkpointSizeLabel = toolkit.createLabel(body, "Checkpoint size (kbytes):");
        m_checkpointSizeText = toolkit.createText(body, "");
        gd = new GridData();
        gd.minimumWidth = 100;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_checkpointSizeText.setLayoutData(gd);
        m_checkpointDeleteButton = toolkit.createButton(body, "Delete Checkpoint", SWT.PUSH);
        m_checkpointDeleteButton.addSelectionListener(new SelectionListener() {
            /*
             * (non-Javadoc)
             * @see org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse.swt.events.SelectionEvent)
             */
			public void widgetSelected(SelectionEvent e) {
				final IResource[] checkpoints;
				try {
					checkpoints = getModel().getCheckpoints(false);

					if ((checkpoints != null) && checkpoints.length > 0) {
						ResourcesPlugin.getWorkspace().run((monitor) -> {
							checkpoints[0].delete(true, SubMonitor.convert(monitor, 1));
						}, null);
					}
				} catch (CoreException e1) {
					return;
				}
			}

			/*
			 * (non-Javadoc)
			 * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
			 */
			public void widgetDefaultSelected(SelectionEvent e) { }
        });
        m_checkpointDeleteButton.addFocusListener(focusListener);
        new Label(body, SWT.NONE); // use up last cell.

        // Collect Coverage
		final String collectCoverageHelp = "Coverage helps identify problems with the specification such as action which are "
				+ "never enabled. Cost statistics allow to diagnose expensive expressions to evaluate and state space "
				+ "explosion. Both statistics negatively impact model checking performance and should thus be disabled while "
				+ "checking large models.";
		final Label collectCoverageLabel = toolkit.createLabel(body,
				"Collect coverage and cost statistics during model checking:");
        gd = new GridData();
        gd.verticalIndent = 9;
        collectCoverageLabel.setLayoutData(gd);
        collectCoverageLabel.setToolTipText(collectCoverageHelp);

        m_collectCoverageCheckbox = toolkit.createButton(body, "", SWT.CHECK);
        gd = new GridData();
        gd.verticalIndent = 9;
        m_collectCoverageCheckbox.setLayoutData(gd);
        m_collectCoverageCheckbox.addFocusListener(focusListener);
        m_collectCoverageCheckbox.setToolTipText(collectCoverageHelp);
        
        hr = toolkit.createSeparator(body, SWT.HORIZONTAL);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalSpan = 2;
        gd.verticalIndent = 6;
        hr.setLayoutData(gd);
        
        // label deferred liveness checking
		final String deferLivenessHelp = "Defer verification of temporal properties (liveness) to the end of model checking"
				+ " to reduce overall model checking time. Liveness violations will be found late compared to invariant "
				+ "violations. In other words check liveness only once on the complete state space.";
        final Label deferLivenessLabel = toolkit.createLabel(body, "Verify temporal properties upon termination only:");
        gd = new GridData();
        gd.verticalIndent = 6;
        deferLivenessLabel.setLayoutData(gd);
		deferLivenessLabel.setToolTipText(deferLivenessHelp);

        m_deferLivenessCheckbox = toolkit.createButton(body, "", SWT.CHECK);
        m_deferLivenessCheckbox.addFocusListener(focusListener);
        m_deferLivenessCheckbox.setToolTipText(deferLivenessHelp);
        gd = new GridData();
        gd.verticalIndent = 6;
        m_deferLivenessCheckbox.setLayoutData(gd);
       
        // label fp
        toolkit.createLabel(body, "Fingerprint seed index:");
      
        final Composite fpIndex = toolkit.createComposite(body);
        gl = new GridLayout(2, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        fpIndex.setLayout(gl);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        fpIndex.setLayoutData(gd);
        
        m_randomFingerprintCheckbox = toolkit.createButton(fpIndex, "Select randomly", SWT.CHECK);
		m_randomFingerprintCheckbox.setToolTipText(
				"Let TLC randomly choose the irreducible polynomial at startup. The actual value will be shon in TLC's startup banner.");
        m_randomFingerprintCheckbox.setSelection(true);
        m_randomFingerprintCheckbox.addFocusListener(focusListener);
        m_randomFingerprintCheckbox.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				m_fingerprintSeedIndex.setEnabled(!m_randomFingerprintCheckbox.getSelection());
			}
		});
        
        // field fpIndex
        m_fingerprintSeedIndex = new Spinner(fpIndex, SWT.NONE);
        m_fingerprintSeedIndex.setEnabled(false);
		m_fingerprintSeedIndex.setToolTipText(
				"Index of irreducible polynominal used as a seed for fingerprint hashing (corresponds to \"-fp value\"). Set to the irreducible polynomial used for the previous run if \"Select randomly\" checked.");
        gd = new GridData();
        gd.horizontalIndent = 15;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_fingerprintSeedIndex.setLayoutData(gd);
        
        // validation for fpIndex spinner
        m_fingerprintSeedIndex.setMinimum(0);
        m_fingerprintSeedIndex.setMaximum(FP64.Polys.length - 1);
        
        m_fingerprintSeedIndex.addFocusListener(focusListener);
        
        // fpbits label
        toolkit.createLabel(body, "Log base 2 of number of disk storage files:");

        // fpbits spinner
        m_fingerprintBits = new Spinner(body, SWT.NONE);
        m_fingerprintBits.setData(FormToolkit.KEY_DRAW_BORDER, FormToolkit.TEXT_BORDER);
        m_fingerprintBits.addFocusListener(focusListener);
        gd = new GridData();
        gd.verticalIndent = 20;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_fingerprintBits.setLayoutData(gd);

        m_fingerprintBits.setMinimum(MultiFPSet.MIN_FPBITS);
        m_fingerprintBits.setMaximum(MultiFPSet.MAX_FPBITS);

        final int defaultFPBits = TLCUIActivator.getDefault().getPreferenceStore().getInt(
        		ITLCPreferenceConstants.I_TLC_FPBITS_DEFAULT);
        m_fingerprintBits.setSelection(defaultFPBits);
        
        // maxSetSize label
        toolkit.createLabel(body, "Cardinality of largest enumerable set:");
        
        // maxSetSize spinner
        m_maxSetSize = new Spinner(body, SWT.NONE);
        m_maxSetSize.setData( FormToolkit.KEY_DRAW_BORDER, FormToolkit.TEXT_BORDER );
        m_maxSetSize.addFocusListener(focusListener);
        gd = new GridData();
        gd.verticalIndent = 20;
        gd.minimumWidth = 100;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_maxSetSize.setLayoutData(gd);

        m_maxSetSize.setMinimum(1);
        m_maxSetSize.setMaximum(Integer.MAX_VALUE);

        final int defaultMaxSetSize = TLCUIActivator.getDefault().getPreferenceStore().getInt(
        		ITLCPreferenceConstants.I_TLC_MAXSETSIZE_DEFAULT);
        m_maxSetSize.setSelection(defaultMaxSetSize);
        
        // Visualize State Graph with GraphViz (dot)
		final String visualizeStateGraphHelp = "Draw the state graph after completion of model checking provided the "
				+ "state graph is sufficiently small (cannot handle more than a few dozen states and slows down model checking).";
        final Label visualizeStateGraphLabel = toolkit.createLabel(body, "Visualize state graph after completion of model checking:");
        gd = new GridData();
        gd.verticalIndent = 9;
        visualizeStateGraphLabel.setLayoutData(gd);
        visualizeStateGraphLabel.setToolTipText(visualizeStateGraphHelp);

        m_visualizeStateGraphCheckbox = toolkit.createButton(body, "", SWT.CHECK);
        gd = new GridData();
        gd.verticalIndent = 9;
        m_visualizeStateGraphCheckbox.setLayoutData(gd);
        m_visualizeStateGraphCheckbox.addFocusListener(focusListener);
        m_visualizeStateGraphCheckbox.setToolTipText(visualizeStateGraphHelp);
    
		// Extra/Additional VM arguments and system properties
        toolkit.createLabel(body, "JVM arguments:");

        m_extraVMArgumentsText = toolkit.createText(body, "", SWT.MULTI | SWT.WRAP | SWT.V_SCROLL);
        m_extraVMArgumentsText.setEditable(true);
		m_extraVMArgumentsText.setToolTipText(
				"Optionally pass additional JVM arguments to TLC process (e.g. -Djava.rmi.server.hostname=ThisHostName)");
        m_extraVMArgumentsText.addFocusListener(focusListener);
        gd = new GridData();
        gd.verticalIndent = 20;
        gd.heightHint = 40;
        gd.minimumWidth = 300;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_extraVMArgumentsText.setLayoutData(gd);

		// Extra/Additional TLC arguments
        toolkit.createLabel(body, "TLC command line parameters:");

        m_extraTLCParametersText = toolkit.createText(body, "", SWT.MULTI | SWT.WRAP | SWT.V_SCROLL);
        m_extraTLCParametersText.setEditable(true);
		m_extraTLCParametersText
				.setToolTipText("Optionally pass additional TLC process parameters (e.g. -Dcheckpoint 0)");
        m_extraTLCParametersText.addFocusListener(focusListener);
        gd = new GridData();
        gd.verticalIndent = 20;
        gd.heightHint = 40;
        gd.minimumWidth = 300;
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        m_extraTLCParametersText.setLayoutData(gd);
        
        updateEnabledStatesForAdvancedLaunchRadioSelection();

        dm.bindAttribute(MODEL_PARAMETER_VIEW, m_viewSource, launchPart);
        dm.bindAttribute(LAUNCH_RECOVER, m_checkpointRecoverCheckbox, launchPart);
        
        // dirty listeners
        m_simulationArilText.addModifyListener(launchListener);
        m_simulationSeedText.addModifyListener(launchListener);
        m_simulationDepthText.addModifyListener(launchListener);
        m_fingerprintSeedIndex.addModifyListener(launchListener);
        m_randomFingerprintCheckbox.addSelectionListener(launchListener);
        m_fingerprintBits.addModifyListener(launchListener);
        m_maxSetSize.addModifyListener(launchListener);
        m_depthText.addModifyListener(launchListener);
        m_simulationModeOption.addSelectionListener(launchListener);
        m_deferLivenessCheckbox.addSelectionListener(launchListener);
        m_depthFirstOptionCheckbox.addSelectionListener(launchListener);
        m_modelCheckModeOption.addSelectionListener(launchListener);
        m_checkpointRecoverCheckbox.addSelectionListener(launchListener);
        m_viewSource.addTextListener(launchListener);
        m_visualizeStateGraphCheckbox.addSelectionListener(launchListener);
        m_collectCoverageCheckbox.addSelectionListener(launchListener);
        m_extraTLCParametersText.addModifyListener(launchListener);
        m_extraVMArgumentsText.addModifyListener(launchListener);

        // add section ignoring listeners
        dirtyPartListeners.add(launchListener);
    }

    /**
     * Loads data from the model
     */
    @Override
	protected void loadData() throws CoreException {
    	final Model model = getModel();

    	// view
        final String view = model.getAttribute(LAUNCH_VIEW, EMPTY_STRING);
        m_viewSource.setDocument(new Document(view));

        // run mode mode
        final boolean isMCMode = model.getAttribute(LAUNCH_MC_MODE, LAUNCH_MC_MODE_DEFAULT);
        m_modelCheckModeOption.setSelection(isMCMode);
        m_simulationModeOption.setSelection(!isMCMode);

        // DFID depth
        final int dfidDepth = model.getAttribute(LAUNCH_DFID_DEPTH, LAUNCH_DFID_DEPTH_DEFAULT);
        m_depthText.setText("" + dfidDepth);

        // DFID mode
        final boolean isDFIDMode = model.getAttribute(LAUNCH_DFID_MODE, LAUNCH_DFID_MODE_DEFAULT);
        m_depthFirstOptionCheckbox.setSelection(isDFIDMode);
        m_depthText.setEnabled(isDFIDMode);

        // simulation depth
        final int simuDepth = model.getAttribute(LAUNCH_SIMU_DEPTH, LAUNCH_SIMU_DEPTH_DEFAULT);
        m_simulationDepthText.setText("" + simuDepth);

        // simulation aril
		final int simuAril = model.getAttribute(LAUNCH_SIMU_SEED, LAUNCH_SIMU_ARIL_DEFAULT);
		if (LAUNCH_SIMU_ARIL_DEFAULT != simuAril) {
			m_simulationArilText.setText("" + simuAril);
		} else {
			m_simulationArilText.setText("");
		}

        // simulation seed
		final int simuSeed = model.getAttribute(LAUNCH_SIMU_ARIL, LAUNCH_SIMU_SEED_DEFAULT);
		if (LAUNCH_SIMU_SEED_DEFAULT != simuSeed) {
			m_simulationSeedText.setText("" + simuSeed);
		} else {
			m_simulationSeedText.setText("");
		}
        
        // Defer Liveness
		m_deferLivenessCheckbox.setSelection(model.getAttribute(LAUNCH_DEFER_LIVENESS, LAUNCH_DEFER_LIVENESS_DEFAULT));

        // recover from the checkpoint
        final boolean recover = model.getAttribute(LAUNCH_RECOVER, LAUNCH_RECOVER_DEFAULT);
        m_checkpointRecoverCheckbox.setSelection(recover);
        
        // coverage
        m_collectCoverageCheckbox.setSelection(model.getAttribute(LAUNCH_COVERAGE, LAUNCH_COVERAGE_DEFAULT));
        
        // fp index
        final boolean randomly = model.getAttribute(LAUNCH_FP_INDEX_RANDOM, LAUNCH_FP_INDEX_RANDOM_DEFAULT);
        m_randomFingerprintCheckbox.setSelection(randomly);
        final int fpIndex = model.getAttribute(LAUNCH_FP_INDEX, LAUNCH_FP_INDEX_DEFAULT);
        m_fingerprintSeedIndex.setSelection(fpIndex);
        m_fingerprintSeedIndex.setEnabled(!randomly);

        // fpBits
        final int defaultFPBits = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_FPBITS_DEFAULT);
        m_fingerprintBits.setSelection(model.getAttribute(LAUNCH_FPBITS, defaultFPBits));

        // maxSetSize
        final int defaultMaxSetSize = TLCUIActivator.getDefault().getPreferenceStore().getInt(
                ITLCPreferenceConstants.I_TLC_MAXSETSIZE_DEFAULT);
        m_maxSetSize.setSelection(model.getAttribute(LAUNCH_MAXSETSIZE, defaultMaxSetSize));
        
        // visualize state graph
        m_visualizeStateGraphCheckbox.setSelection(model.getAttribute(LAUNCH_VISUALIZE_STATEGRAPH, LAUNCH_VISUALIZE_STATEGRAPH_DEFAULT));
        
        // Extra JVM arguments and system properties
        final String vmArgs = model.getAttribute(LAUNCH_JVM_ARGS, LAUNCH_JVM_ARGS_DEFAULT);
        m_extraVMArgumentsText.setText(vmArgs);

        // Extra JVM arguments and system properties
        final String tlcParameters = model.getAttribute(LAUNCH_TLC_PARAMETERS, LAUNCH_TLC_PARAMETERS_DEFAULT);
        m_extraTLCParametersText.setText(tlcParameters);
        
        // it should still be true here from the body content creation invocation, but in case not:
        programmaticallySettingWorkerParameters.set(true);
		workers.setSelection(mainModelPage.getWorkerCount());
        maxHeapSize.setSelection(mainModelPage.getHeapPercentage());
        programmaticallySettingWorkerParameters.set(false);
        setWorkerAndMemoryEnable(mainModelPage.workerCountCanBeModified(), mainModelPage.heapPercentageCanBeModified());
        
        updateEnabledStatesForAdvancedLaunchRadioSelection();
    }

    /**
     * Save data back to config
     */
    @Override
	public void commit(final boolean onSave) {
    	final Model model = getModel();
		
        final boolean isMCMode = m_modelCheckModeOption.getSelection();
        model.setAttribute(LAUNCH_MC_MODE, isMCMode);

        // DFID mode
        final boolean isDFIDMode = m_depthFirstOptionCheckbox.getSelection();
        model.setAttribute(LAUNCH_DFID_MODE, isDFIDMode);
        final int dfidDepth = Integer.parseInt(m_simulationDepthText.getText());
        
        final int simuDepth = Integer.parseInt(m_simulationDepthText.getText());
        int simuAril = LAUNCH_SIMU_ARIL_DEFAULT;
        int simuSeed = LAUNCH_SIMU_SEED_DEFAULT;

		if (!"".equals(m_simulationArilText.getText())) {
			simuAril = Integer.parseInt(m_simulationArilText.getText());
		}
		if (!"".equals(m_simulationSeedText.getText())) {
			simuSeed = Integer.parseInt(m_simulationSeedText.getText());
		}

        // DFID depth
		model.setAttribute(LAUNCH_DFID_DEPTH, dfidDepth);
        // simulation depth
		model.setAttribute(LAUNCH_SIMU_DEPTH, simuDepth);
        // simulation aril
		model.setAttribute(LAUNCH_SIMU_SEED, simuSeed);
        // simulation seed
		model.setAttribute(LAUNCH_SIMU_ARIL, simuAril);

        // Defer Liveness
		model.setAttribute(LAUNCH_DEFER_LIVENESS, m_deferLivenessCheckbox.getSelection());

        // recover from deadlock
		model.setAttribute(LAUNCH_RECOVER, m_checkpointRecoverCheckbox.getSelection());
        
        // FP Seed choose randomly
		model.setAttribute(LAUNCH_FP_INDEX_RANDOM, m_randomFingerprintCheckbox.getSelection());
		// FP Seed index
		model.setAttribute(LAUNCH_FP_INDEX, m_fingerprintSeedIndex.getSelection());

        // fpBits
		model.setAttribute(LAUNCH_FPBITS, m_fingerprintBits.getSelection());

        // fpBits
		model.setAttribute(LAUNCH_MAXSETSIZE, m_maxSetSize.getSelection());

        // Visualize State Graph
		model.setAttribute(LAUNCH_VISUALIZE_STATEGRAPH, m_visualizeStateGraphCheckbox.getSelection());

        // Collect Coverage
		model.setAttribute(LAUNCH_COVERAGE, m_collectCoverageCheckbox.getSelection());
       
        // view
        String viewFormula = FormHelper.trimTrailingSpaces(m_viewSource.getDocument().get());
        model.setAttribute(LAUNCH_VIEW, viewFormula);

		// extra vm arguments (replace newlines which otherwise cause the
		// process to ignore all args except the first one)
        final String vmArgs = m_extraVMArgumentsText.getText().replace("\r\n", " ").replace("\n", " ");
        model.setAttribute(LAUNCH_JVM_ARGS, vmArgs);

        // extra tlc parameters
        final String tlcParameters = m_extraTLCParametersText.getText();
        model.setAttribute(LAUNCH_TLC_PARAMETERS, tlcParameters);
      
        super.commit(onSave);
    }

    /**
     * Validate the page's state.
     */
	@Override
	public void validatePage(final boolean switchToErrorPage) {
		if (getManagedForm() == null) {
			return;
		}
		
        final DataBindingManager dm = getDataBindingManager();
        final IMessageManager mm = getManagedForm().getMessageManager();
        mm.setAutoUpdate(false);

        final ModelEditor modelEditor = (ModelEditor) getEditor();

        // clean old messages
        // this is now done in validateRunnable of
        // ModelEditor
        // mm.removeAllMessages();
        // make the run possible
        setComplete(true);

        // setup the names from the current page
        getLookupHelper().resetModelNames(this);

        // number of workers
    	int number = workers.getSelection();
        if (number > Runtime.getRuntime().availableProcessors())
        {
            modelEditor.addErrorMessage("strangeNumber1", "Specified number of workers is " + number
                    + ". The number of processors available on the system is "
                    + Runtime.getRuntime().availableProcessors()
                    + ".\n The number of workers should not exceed the number of processors.",
                    this.getId(), IMessageProvider.WARNING, UIHelper.getWidget(dm
					        .getAttributeControl(LAUNCH_NUMBER_OF_WORKERS)));
            expandSection(SEC_HOW_TO_RUN);
        } else {
        	modelEditor.removeErrorMessage("strangeNumber1", UIHelper.getWidget(dm
			        .getAttributeControl(LAUNCH_NUMBER_OF_WORKERS)));
        }
        
		// legacy value?
		// better handle legacy models
		try {
			final int defaultMaxHeapSize = TLCUIActivator
					.getDefault()
					.getPreferenceStore()
					.getInt(ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT);
			final int legacyValue = getModel().getAttribute(
					LAUNCH_MAX_HEAP_SIZE, defaultMaxHeapSize);
			// old default, silently convert to new default
			if (legacyValue == 500) {
				getModel().setAttribute(
						LAUNCH_MAX_HEAP_SIZE, TLCPreferenceInitializer.MAX_HEAP_SIZE_DEFAULT);
				maxHeapSize.setSelection(TLCPreferenceInitializer.MAX_HEAP_SIZE_DEFAULT);
			} else if (legacyValue >= 100) {
				modelEditor
						.addErrorMessage(
								"strangeNumber1",
								"Found legacy value for physically memory of ("
										+ legacyValue
										+ "mb) that needs manual conversion. 25% is a safe setting on most computers.",
								this.getId(), IMessageProvider.WARNING,
								maxHeapSize);
				setComplete(false);
				expandSection(SEC_HOW_TO_RUN);
			}
		} catch (CoreException e) {
			TLCUIActivator.getDefault().logWarning("Faild to read heap value", e);
		}
        
        // max heap size
		// color the scale according to OS and TLC requirements
        int maxHeapSizeValue = maxHeapSize.getSelection();
		double x = maxHeapSizeValue / 100d;
		float y = (float) linearInterpolator.interpolate(x);
		maxHeapSize.setBackground(new Color(Display.getDefault(), new RGB(120 * y, 1 - y, 1f)));

		try {
			int dfidDepth = Integer.parseInt(m_depthText.getText());
			if (dfidDepth <= 0) {
				modelEditor.addErrorMessage("dfid1", "Depth of DFID launch must be a positive integer", this.getId(),
						IMessageProvider.ERROR, m_depthText);
				setComplete(false);
				expandSection(SEC_LAUNCHING_SETUP);
			} else {
				// Call of removeErrorMessage added by LL on 21 Mar 2013
				modelEditor.removeErrorMessage("dfid1", m_depthText);
			}
			// Call of removeErrorMessage added by LL on 21 Mar 2013
			modelEditor.removeErrorMessage("dfid2", m_depthText);
		} catch (NumberFormatException e) {
			modelEditor.addErrorMessage("dfid2", "Depth of DFID launch must be a positive integer", this.getId(),
					IMessageProvider.ERROR, m_depthText);
			setComplete(false);
			expandSection(SEC_LAUNCHING_SETUP);
		}
		try {
			int simuDepth = Integer.parseInt(m_simulationDepthText.getText());
			if (simuDepth <= 0) {
				modelEditor.addErrorMessage("simuDepth1", "Length of the simulation tracemust be a positive integer",
						this.getId(), IMessageProvider.ERROR, m_simulationDepthText);
				setComplete(false);
				expandSection(SEC_LAUNCHING_SETUP);
			} else {
				// Call of removeErrorMessage added by LL on 21 Mar 2013
				modelEditor.removeErrorMessage("simuDepth1", m_simulationDepthText);
			}
			// Call of removeErrorMessage added by LL on 21 Mar 2013
			modelEditor.removeErrorMessage("simuDepth2", m_simulationDepthText);
		} catch (NumberFormatException e) {
			modelEditor.addErrorMessage("simuDepth2", "Length of the simulation trace must be a positive integer",
					this.getId(), IMessageProvider.ERROR, m_simulationDepthText);
			setComplete(false);
			expandSection(SEC_LAUNCHING_SETUP);
		}
		if (!EMPTY_STRING.equals(m_simulationArilText.getText())) {
			try {
				long simuAril = Long.parseLong(m_simulationArilText.getText());
				if (simuAril <= 0) {
					modelEditor.addErrorMessage("simuAril1", "The simulation aril must be a positive integer",
							this.getId(), IMessageProvider.ERROR, m_simulationArilText);
					setComplete(false);
				} else {
					// Call of removeErrorMessage added by LL on 21 Mar 2013
					modelEditor.removeErrorMessage("simuAril1", m_simulationArilText);
				}
				// Call of removeErrorMessage added by LL on 21 Mar 2013
				modelEditor.removeErrorMessage("simuAril2", m_simulationArilText);
			} catch (NumberFormatException e) {
				modelEditor.addErrorMessage("simuAril2", "The simulation aril must be a positive integer", this.getId(),
						IMessageProvider.ERROR, m_simulationArilText);
				setComplete(false);
				expandSection(SEC_LAUNCHING_SETUP);
			}
		}
		if (!EMPTY_STRING.equals(m_simulationSeedText.getText())) {
			try {
				Long.parseLong(m_simulationSeedText.getText());
				// Call of removeErrorMessage added by LL on 21 Mar 2013
				modelEditor.removeErrorMessage("simuSeed1", m_simulationSeedText);

			} catch (NumberFormatException e) {
				modelEditor.addErrorMessage("simuSeed1", "The simulation aril must be a positive integer", this.getId(),
						IMessageProvider.ERROR, m_simulationSeedText);
				expandSection(SEC_LAUNCHING_SETUP);
				setComplete(false);
			}
		}

        // fill the checkpoints
        updateCheckpoints();

        // recover from checkpoint
        final Control checkpointRecover = UIHelper.getWidget(dm.getAttributeControl(LAUNCH_RECOVER));
        modelEditor.removeErrorMessage("noCheckpoint", checkpointRecover);
		if (m_checkpointRecoverCheckbox.getSelection()) {
			if (EMPTY_STRING.equals(m_checkpointIdText.getText())) {
				modelEditor.addErrorMessage("noCheckpoint", "No checkpoint data found", this.getId(),
						IMessageProvider.ERROR, checkpointRecover);
				setComplete(false);
				expandSection(SEC_LAUNCHING_SETUP);
			}
		}

        // check if the view field contains a cfg file keyword
        final Control viewWidget = UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_VIEW));
        final IDocument viewerDocument = m_viewSource.getDocument();
		if (viewerDocument != null) {
			final String viewString = FormHelper.trimTrailingSpaces(viewerDocument.get());
			if (SemanticHelper.containsConfigFileKeyword(viewString)) {
				modelEditor.addErrorMessage(viewString,
						"The toolbox cannot handle the string " + viewString
								+ " because it contains a configuration file keyword.",
						this.getId(), IMessageProvider.ERROR, viewWidget);
				setComplete(false);
			}
		}

        mm.setAutoUpdate(true);

                
        // fpBits
        if (!FPSet.isValid(m_fingerprintBits.getSelection()))
        {
            modelEditor.addErrorMessage("wrongNumber3", "fpbits must be a positive integer number smaller than 31", this
					.getId(), IMessageProvider.ERROR, UIHelper.getWidget(dm.getAttributeControl(LAUNCH_FPBITS)));
            setComplete(false);
            expandSection(SEC_HOW_TO_RUN);
        }
//        else {
//            // Call of removeErrorMessage added by LL on 21 Mar 2013
//            // However, it seems to be a no-op because you can't enter an illegal
//            // value into the widget.  I've commented this out in case it has some
//            // unknown evil side effects.
//            modelEditor.removeErrorMessage("wrongNumber3", 
//                                            UIHelper.getWidget(dm.getAttributeControl(LAUNCH_FPBITS)));
//          }
        
        // maxSetSize
        if (!TLCGlobals.isValidSetSize(m_maxSetSize.getSelection()))
        {
            modelEditor.addErrorMessage("wrongNumber3", "maxSetSize must be a positive integer number", this.getId(),
            		IMessageProvider.ERROR, UIHelper.getWidget(dm.getAttributeControl(LAUNCH_MAXSETSIZE)));
            setComplete(false);
            expandSection(SEC_HOW_TO_RUN);
        }
//        else {
//        // Call of removeErrorMessage added by LL on 21 Mar 2013
//        // However, it seems to be a no-op because you can't enter an illegal
//        // value into the widget, so this was all commented out.
//        modelEditor.removeErrorMessage("wrongNumber3", 
//                                        UIHelper.getWidget(dm.getAttributeControl(LAUNCH_MAXSETSIZE)));
//        }
        
        super.validatePage(switchToErrorPage);
    }
	
    /**
     * Checks if checkpoint information changed 
     */
	private void updateCheckpoints() {
		IResource[] checkpoints = null;
		try {
			// checkpoint id
			checkpoints = getModel().getCheckpoints(false);
		} catch (CoreException e) {
			TLCUIActivator.getDefault().logError("Error checking chekpoint data", e);
		}

		if (checkpoints != null && checkpoints.length > 0) {
			m_checkpointIdText.setText(checkpoints[0].getName());
		} else {
			m_checkpointIdText.setText(EMPTY_STRING);
		}

		if ((checkpoints == null) || (checkpoints.length == 0)) {
			m_checkpointSizeText.setVisible(false);
			m_checkpointSizeLabel.setVisible(false);
			m_checkpointDeleteButton.setVisible(false);
		} else {
			m_checkpointSizeText.setText(String.valueOf(ResourceHelper.getSizeOfJavaFileResource(checkpoints[0]) / 1000));
			m_checkpointSizeText.setVisible(true);
			m_checkpointSizeLabel.setVisible(true);
			m_checkpointDeleteButton.setVisible(true);
		}
	}
    
    private void updateEnabledStatesForAdvancedLaunchRadioSelection () {
    	final boolean simulationMode = m_simulationModeOption.getSelection();
    	
    	m_viewSource.getTextWidget().setEnabled(!simulationMode);
    	m_depthFirstOptionCheckbox.setEnabled(!simulationMode);
    	if (simulationMode) {
    		m_depthText.setEnabled(false);
    	} else {
    		m_depthText.setEnabled(m_depthFirstOptionCheckbox.getSelection());
    	}
    	
    	m_simulationDepthText.setEnabled(simulationMode);
    	m_simulationSeedText.setEnabled(simulationMode);
    	m_simulationArilText.setEnabled(simulationMode);
    }
    
    public void updateWorkersAndMemory(final int workerCount, final int memoryPercentage) {
		programmaticallySettingWorkerParameters.set(true);

		workers.setSelection(workerCount);
		maxHeapSize.setSelection(memoryPercentage);
    	
		programmaticallySettingWorkerParameters.set(false);
    }
    
	public void setWorkerAndMemoryEnable(final boolean enableWorker, final boolean enableMaxHeap) {
    	workers.getDisplay().asyncExec(() -> {
    		workers.setEnabled(enableWorker);
    		maxHeapSize.setEnabled(enableMaxHeap);
    	});
    }

	public void setFpIndex(final int fpIndex) {
		if (m_fingerprintSeedIndex.getSelection() == fpIndex) {
			return;
		}
		// Temporarily disable all modify listeners to prevent the model from becoming
		// dirty. We don't want the model to become dirty as a result of model checking.
		final Listener[] listeners = this.m_fingerprintSeedIndex.getListeners(SWT.Modify);
		for (Listener listener : listeners) {
			m_fingerprintSeedIndex.removeListener(SWT.Modify, listener);
		}
		
		m_fingerprintSeedIndex.setSelection(fpIndex);
		
		for (Listener listener : listeners) {
			m_fingerprintSeedIndex.addListener(SWT.Modify, listener);
		}
	}

	@Override
	public void close() throws IOException {
		final int openTabState = getModel().getOpenTabsValue();
		getModelEditor().updateOpenTabsState(openTabState & ~IModelConfigurationConstants.EDITOR_OPEN_TAB_ADVANCED_TLC);
	}
    
    private String generateMemoryDisplayText () {
		final int percentage = maxHeapSize.getSelection();
		final long megabytes = TLCRuntime.getInstance().getAbsolutePhysicalSystemMemory(percentage / 100d);

		return MainModelPage.generateMemoryDisplayText(percentage, megabytes);
    }

    
    /**
     * Interpolates based on LinearInterpolation
     */
    private class Interpolator {

    	private final double[] yCoords, xCoords;

    	public Interpolator(double[] x, double[] y) {
    		this.xCoords = x;
    		this.yCoords = y;
    	}

		public double interpolate(double x) {
			for (int i = 1; i < xCoords.length; i++) {
				if (x < xCoords[i]) {
					return yCoords[i] - (yCoords[i] - yCoords[i - 1])
							* (xCoords[i] - x) / (xCoords[i] - xCoords[i - 1]);
				}
			}
			return 0d;
		}
    }
}
