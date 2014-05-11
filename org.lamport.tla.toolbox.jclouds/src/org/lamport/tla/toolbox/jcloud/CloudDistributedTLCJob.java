package org.lamport.tla.toolbox.jcloud;

import static com.google.common.base.Predicates.not;
import static org.jclouds.compute.predicates.NodePredicates.TERMINATED;
import static org.jclouds.compute.predicates.NodePredicates.inGroup;
import static org.jclouds.scriptbuilder.domain.Statements.exec;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Path;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;
import java.util.UUID;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.jclouds.ContextBuilder;
import org.jclouds.aws.ec2.reference.AWSEC2Constants;
import org.jclouds.compute.ComputeService;
import org.jclouds.compute.ComputeServiceContext;
import org.jclouds.compute.RunNodesException;
import org.jclouds.compute.RunScriptOnNodesException;
import org.jclouds.compute.domain.ExecResponse;
import org.jclouds.compute.domain.NodeMetadata;
import org.jclouds.compute.domain.TemplateBuilder;
import org.jclouds.compute.options.TemplateOptions;
import org.jclouds.io.Payload;
import org.jclouds.scriptbuilder.domain.Statement;
import org.jclouds.scriptbuilder.statements.java.InstallJDK;
import org.jclouds.scriptbuilder.statements.login.AdminAccess;
import org.jclouds.ssh.SshClient;
import org.jclouds.sshj.config.SshjSshClientModule;
import org.lamport.tla.toolbox.tool.tlc.job.ITLCJobStatus;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJobFactory;

import com.google.common.base.Predicate;
import com.google.common.base.Predicates;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.inject.AbstractModule;

public class CloudDistributedTLCJob extends Job {

	// ubuntu official
	public static final String OWNER_ID_CANONICAL_LTD = "owner-id=owner-id=099720109477;state=available;image-type=machine";
	// instance store/paravirtual/amd64/ubuntu/server
	public static final String US_EAST_UBUNTU_14_04_AMD64 = "us-east-1/ami-7fe7fe16"; // ubuntu 64bit 14.04 precise
	public static final String EU_WEST_UBUNTU_12_04_AMD64 = "eu-west-1/ami-036eaa74";
	
	private final String identity = System.getenv("AWS_ACCESS_KEY_ID");
	private final String credential = System
			.getenv("AWS_SECRET_ACCESS_KEY");
	private final Properties props;

	public CloudDistributedTLCJob(String aName, File aModelFolder,
			int numberOfWorkers, final Properties properties) {
		super(aName);
		groupNameUUID = aName + "-" + UUID.randomUUID().toString();
		props = properties;
		modelPath = aModelFolder.toPath();
		
		//TODO Make this configurable
		imageId = US_EAST_UBUNTU_14_04_AMD64;
		ownerId = OWNER_ID_CANONICAL_LTD;
	}

	private final String ownerId;
	private final String imageId;
	private final String cloudProvider = "aws-ec2";
	/**
	 * The groupName has to be unique per job. This is how cloud instances are
	 * associated to this job. If two jobs use the same groupName, the will talk
	 * to the same set of nodes.
	 */
	private final String groupNameUUID;
	
	private Path modelPath;
	private final int nodes = 1; //TODO only supports launching TLC on a single node for now

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.lamport.tla.toolbox.tool.tlc.job.TLCJob#run(org.eclipse.core.runtime
	 * .IProgressMonitor)
	 */
	@Override
	protected IStatus run(final IProgressMonitor monitor) {
		monitor.beginTask("Starting TLC model checker in the cloud", 85);
		
		ComputeServiceContext context = null;
		try {
			final Payload jarPayLoad = PayloadHelper
					.appendModel2Jar(modelPath,
							props.getProperty(TLCJobFactory.MAIN_CLASS), props,
							monitor);
			// User has canceled the job, thus stop it (there will be more
			// cancelled checks down below).
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}

			// example of specific properties, in this case optimizing image
			// list to
			// only amazon supplied
			final Properties properties = new Properties();
			properties
			.setProperty(
					AWSEC2Constants.PROPERTY_EC2_AMI_QUERY,
					ownerId);
//			properties.setProperty(AWSEC2Constants.PROPERTY_EC2_CC_REGIONS, "eu-west-1");

			// Create compute environment in the cloud and inject an ssh
			// implementation. ssh is our means of communicating with the node.
			final Iterable<AbstractModule> modules = ImmutableSet
					.<AbstractModule> of(new SshjSshClientModule());

			final ContextBuilder builder = ContextBuilder
					.newBuilder(cloudProvider)
					.credentials(identity, credential).modules(modules)
					.overrides(properties);

			monitor.subTask("Initializing " + builder.getApiMetadata().getName());
			context = builder.buildView(ComputeServiceContext.class);
			final ComputeService compute = context.getComputeService();
			monitor.worked(10);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}
			
			// start a node, but first configure it
			final TemplateOptions templateOptions = compute.templateOptions();
			
			// Open up node's firewall to allow http traffic in. This allows users to 
			// look at the munin/ stats generated for the OS as well as TLC specifically.
			// (See below where munin gets installed manually)
			// This now makes us dependent on EC2 (for now)
			templateOptions.inboundPorts(22, 80);
			
			// note this will create a user with the same name as you on the
			// node. ex. you can connect via ssh public IP
			templateOptions.runScript(AdminAccess.standard());
			
            TemplateBuilder templateBuilder = compute.templateBuilder();
            templateBuilder.options(templateOptions);
            templateBuilder.imageId(imageId);
            //TODO Support faster/bigger types then just 'small'
            templateBuilder.hardwareId("m3.2xlarge");
//            templateBuilder.fastest();

            monitor.subTask("Starting " + nodes + " instance(s).");
			final Set<? extends NodeMetadata> createNodesInGroup;
			createNodesInGroup = compute.createNodesInGroup(groupNameUUID,
					nodes, templateBuilder.build());
			monitor.worked(20);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}

            // Install Java
			monitor.subTask("Provisioning Java on all node(s)");
            Statement installOpenJDK = InstallJDK.fromOpenJDK();
			Map<? extends NodeMetadata, ExecResponse> responses = compute
					.runScriptOnNodesMatching(
							inGroup(groupNameUUID),
							installOpenJDK);
			monitor.worked(20);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}
			
			// Install custom tailored jmx2munin to monitor the TLC process. Can
			// either monitor standalone tlc2.TLC or TLCServer.
			monitor.subTask("Provisioning TLC Monitoring on all node(s)");
			responses = compute.runScriptOnNodesMatching(
					inGroup(groupNameUUID),
					// Never be prompted for input
					exec("export DEBIAN_FRONTEND=noninteractive && "
							// Download jmx2munin from the INRIA host
							// TODO make it part of Toolbox and upload from
							// there (it's tiny 48kb anyway) instead.
							// This needs some better build-time integration
							// between TLA and jmx2munin (probably best to make
							// jmx2munin a submodule of the TLA git repo).
							+ "wget http://tla.msr-inria.inria.fr/jmx2munin/jmx2munin_1.0_all.deb && "
							// Install jmx2munin into the system
							+ "dpkg -i jmx2munin_1.0_all.deb ; "
							// Force apt to download and install the
							// missing dependencies of jmx2munin without
							// user interaction
							+ "apt-get install -fy && "
							// screen is needed to allow us to re-attach
							// to the TLC process if logged in to the
							// instance directly (it's probably already
							// installed).
							+ "apt-get install screen -y"),
					new TemplateOptions().runAsRoot(true).wrapInInitScript(
							false));			
			monitor.worked(10);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}
			
			// Create /mnt/tlc and change permission to be world writable
			// Requires package 'apache2' to be already installed. apache2
			// creates /var/www/html.
			monitor.subTask("Creating TLC environment on all node(s)");
			responses = compute.runScriptOnNodesMatching(
					inGroup(groupNameUUID),
					exec("mkdir /mnt/tlc/ && "
							+ "chmod 777 /mnt/tlc/ && "
							+ "ln -s /tmp/MC.out /var/www/html/MC.out && "
							+ "ln -s /tmp/MC.err /var/www/html/MC.err"),
					new TemplateOptions().runAsRoot(true).wrapInInitScript(
							false));
			monitor.worked(5);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}

			// TODO CloudD...TLC currently only supports a single tlc2.TLC
			// process. Thus the Predicate and isMaster check is not used for
			// the moment.
			// Choose one of the nodes to be the master and create an
			// identifying predicate.
			monitor.subTask("Copying tla2tools.jar to master node");
			final NodeMetadata master = Iterables.getLast(createNodesInGroup);
			final Predicate<NodeMetadata> isMaster = new Predicate<NodeMetadata>() {
				@Override
				public boolean apply(NodeMetadata nodeMetadata) {
					return nodeMetadata.equals(master);
				};
			};
			// Copy tlatools.jar to _one_ remote host (do not exhaust upload of
			// the machine running the toolbox)
			SshClient sshClient = context.utils().sshForNode().apply(master);
			sshClient.put("/mnt/tlc/tla2tools.jar",	jarPayLoad);
			sshClient.disconnect();
			monitor.worked(10);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}

			// Run model checker master
			monitor.subTask("Starting TLC model checker process on the master node (in background)");
			responses = compute.runScriptOnNodesMatching(
					isMaster,
					// "/mnt/tlc" is on the ephemeral and thus faster storage of the
					// instance.
					exec("cd /mnt/tlc/ && "
							// Execute TLC (java) process inside screen
							// and shutdown on TLC's completion. But
							// detach from screen directly. Name screen 
							// session "tlc".
							// (see http://stackoverflow.com/a/10126799)
//							+ "screen -dm -S tlc bash -c \" "
							// This requires a modified version where all parameters and
							// all spec modules are stored in files in a model/ folder
							// inside of the jar.
							// This is done in anticipation of other cloud providers
							// where one cannot easily pass in parameters on the command
							// line because there is no command line.
							+ "java "
								// These properties cannot be "backed" into
								// the payload jar as java itself does not 
							    // support this.
								// It might be able to read the properties from 
								// the config file with 'com.sun.management.config.file=path',
								// but I haven't tried if the path can point into the jar.
								+ "-Dcom.sun.management.jmxremote "
								+ "-Dcom.sun.management.jmxremote.port=5400 "
								+ "-Dcom.sun.management.jmxremote.ssl=false "
								+ "-Dcom.sun.management.jmxremote.authenticate=false "
								+ "-jar /mnt/tlc/tla2tools.jar && "
							// Let the machine power down immediately after
							// finishing model checking to cut costs. However,
							// do not shut down (hence "&&") when TLC finished
							// with an error.
							// It uses "sudo" because the script is explicitly
							// run as a user. No need to run the TLC process as
							// root.
							// TODO what exit status does TLC show on an error
							// in the spec with a trace?
							+ "sudo shutdown -h now"),
//							+ "\""), // closing opening '"' of screen/bash -c
					new TemplateOptions().runAsRoot(false).wrapInInitScript(
							true).blockOnComplete(false).blockUntilRunning(false));
			monitor.worked(5);

			String endMsg = "";
			URL url = null;
			for (Entry<? extends NodeMetadata, ExecResponse> response : responses
					.entrySet()) {
				
				// TLC nodes only have a single public IP address
				final Set<String> publicAddresses = response.getKey().getPublicAddresses();
				final String[] pubAddr = publicAddresses.toArray(new String[publicAddresses.size()]);
				url = new URL("http://" + pubAddr[0] + "/munin/");
				endMsg = String
						.format("TLC is model checking at host %s. "
								+ "Expect to receive an email for model %s with the model checking result eventually.",
//								+ "In the meantime, progress can be seen at <a href=\"http://%s/munin/\">http://%s/munin/</a> "
//								+ "(it takes approximately five minutes for results to come up. "
//								+ "It shows \"403 Forbidden\" until then.).",
								pubAddr[0], props.get("result.mail.address"));
				monitor.subTask(endMsg);
				System.out.println(endMsg);
				//				System.out.printf(
				//						"<< node %s: %s%n",
				//						response.getKey().getId(),
				//						concat(response.getKey().getPrivateAddresses(),
				//								response.getKey().getPublicAddresses()));
				//				System.out.printf("<<     %s%n", response.getValue());
			}
            
			monitor.done();
			return new CloudStatus(Status.OK, "org.lamport.tla.toolbox.jcloud", Status.OK, endMsg, null, url);
		} catch (RunNodesException|IOException|RunScriptOnNodesException e) {
			e.printStackTrace();
			if (context != null) {
				destroyNodes(context, groupNameUUID);
			}
			// signal error to caller
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					e.getMessage(), e);
		} finally {
			if (context != null) {
				// The user has canceled the Toolbox job, take this as a request
				// to destroy all nodes this job has created.
				if (monitor.isCanceled()) {
					destroyNodes(context, groupNameUUID);
				}
				context.close();
			}
		}
	}

	private static void destroyNodes(final ComputeServiceContext ctx, final String groupname) {
		// Destroy all workers identified by the group
		final ComputeService computeService = ctx.getComputeService();
		if (computeService != null) {
			Set<? extends NodeMetadata> destroyed = computeService
					.destroyNodesMatching(
							Predicates.<NodeMetadata> and(not(TERMINATED),
									inGroup(groupname)));
			System.out.printf("<< destroyed nodes %s%n", destroyed);
		}
	}
	
	class CloudStatus extends Status implements ITLCJobStatus {

		private final URL url;

		public CloudStatus(int severity, String pluginId, int code,
				String message, Throwable exception, URL url) {
			super(severity, pluginId, code, message, exception);
			this.url = url;
		}

		@Override
		public URL getURL() {
			return url;
		}
		
	}

	// /* (non-Javadoc)
	// * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#checkCondition()
	// */
	// @Override
	// protected boolean checkCondition() {
	// //TODO return false once done calculating to end this Job
	// return true;
	// }
}
