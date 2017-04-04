/*******************************************************************************
 * Copyright (c) 2014 Microsoft Research. All rights reserved. 
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

package org.lamport.tla.toolbox.jcloud;

import static com.google.common.base.Predicates.not;
import static org.jclouds.compute.predicates.NodePredicates.TERMINATED;
import static org.jclouds.compute.predicates.NodePredicates.inGroup;
import static org.jclouds.scriptbuilder.domain.Statements.exec;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Path;
import java.util.NoSuchElementException;
import java.util.Properties;
import java.util.Set;
import java.util.UUID;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.jclouds.ContextBuilder;
import org.jclouds.compute.ComputeService;
import org.jclouds.compute.ComputeServiceContext;
import org.jclouds.compute.RunNodesException;
import org.jclouds.compute.RunScriptOnNodesException;
import org.jclouds.compute.domain.NodeMetadata;
import org.jclouds.compute.domain.TemplateBuilder;
import org.jclouds.compute.options.TemplateOptions;
import org.jclouds.io.Payload;
import org.jclouds.logging.slf4j.config.SLF4JLoggingModule;
import org.jclouds.rest.AuthorizationException;
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

/*
 * TODO
 * ====
 * - Reverse PTR records in DNS to make it less likely that emails coming out of the VM are classified as SPAM
 * -- Azure has only support for it in its service API but not in JClouds
 * -- AWS just has a form where users can request a PTR record  
 * - Send test mail during instance startup and communicate back to user on failure
 */
public class CloudDistributedTLCJob extends Job {
	
	/**
	 * The groupName has to be unique per job. This is how cloud instances are
	 * associated to this job. If two jobs use the same groupName, they will talk
	 * to the same set of nodes.
	 */
	private final String groupNameUUID;
	private final Path modelPath;
	private final int nodes;
	private final Properties props;
	private final CloudTLCInstanceParameters params;

	public CloudDistributedTLCJob(String aName, File aModelFolder,
			int numberOfWorkers, final Properties properties, CloudTLCInstanceParameters params) {
		super(aName);
		this.nodes = numberOfWorkers;
		this.params = params;
		//TODO groupNameUUID is used by some providers (azure) as a hostname/DNS name. Thus, format.
		groupNameUUID = aName.toLowerCase() + "-" + UUID.randomUUID().toString();
		props = properties;
		modelPath = aModelFolder.toPath();
	}

	@Override
	protected IStatus run(final IProgressMonitor monitor) {
		final long startUp = System.currentTimeMillis();
		
		monitor.beginTask("Starting TLC model checker in the cloud", 85 + (nodes > 1 ? 20 : 0));
		// Validate credentials and fail fast if null or syntactically incorrect
		if (!params.validateCredentials().equals(Status.OK_STATUS)) {
			return params.validateCredentials();
		}
		
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
			// list to only amazon supplied
			final Properties properties = new Properties();
			params.mungeProperties(properties);

			// Create compute environment in the cloud and inject an ssh
			// implementation. ssh is our means of communicating with the node.
			final Iterable<AbstractModule> modules = ImmutableSet
					.<AbstractModule> of(new SshjSshClientModule(), new SLF4JLoggingModule());

			final ContextBuilder builder = ContextBuilder
					.newBuilder(params.getCloudProvider())
					.credentials(params.getIdentity(), params.getCredentials()).modules(modules)
					.overrides(properties);
			params.mungeBuilder(builder);

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
			templateOptions.inboundPorts(22, 80, 443);
			
			// note this will create a user with the same name as you on the
			// node. ex. you can connect via ssh public IP
			templateOptions.runScript(AdminAccess.standard());
			
            final TemplateBuilder templateBuilder = compute.templateBuilder();
            templateBuilder.options(templateOptions);
            templateBuilder.imageId(params.getImageId());
            templateBuilder.hardwareId(params.getHardwareId());

            // Everything configured, now launch node
            monitor.subTask("Starting " + nodes + " instance(s).");
			final Set<? extends NodeMetadata> createNodesInGroup;
			createNodesInGroup = compute.createNodesInGroup(groupNameUUID,
					nodes, templateBuilder.build());
			monitor.worked(20);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}
			final long spinUp = System.currentTimeMillis();

			// Install custom tailored jmx2munin to monitor the TLC process. Can
			// either monitor standalone tlc2.TLC or TLCServer.
			monitor.subTask("Provisioning TLC environment on all node(s)");
			final String email = props.getProperty(TLCJobFactory.MAIL_ADDRESS);
			compute.runScriptOnNodesMatching(
					inGroup(groupNameUUID),
					// Creating an entry in /etc/alias that makes sure system email sent
					// to root ends up at the address given by the user. Note that this
					// has to be done before postfix gets installed later. postfix
					// re-generates the aliases file for us.
					exec(	"echo root: " + email + " >> /etc/aliases"
							+ " && "
							+ "export DEBIAN_FRONTEND=noninteractive"
							+ " && "
							// Update Ubuntu's package index. The public/remote
							// package mirrors might have updated. Without
							// update, we might try to install outdated packages
							// below. This most likely fails with a 404 because
							// the packages have been purged from the mirrors.
							+ "apt-get update"
							+ " && "
							// Never be prompted for input
							// Download jmx2munin from the INRIA host
							// TODO make it part of Toolbox and upload from
							// there (it's tiny 48kb anyway) instead.
							// This needs some better build-time integration
							// between TLA and jmx2munin (probably best to make
							// jmx2munin a submodule of the TLA git repo).
							// Download an explicit version (commit) to allow
							// us to continue development in HEAD. Otherwise,
							// an old Toolbox would use the newest jmx2munin
							// which might not be compatible with its CDTLCJob.
							+ "wget https://github.com/lemmy/jmx2munin/raw/515e9b47f5a71fbfe2eeb517a341448b52fdb226/jmx2munin_1.0_all.deb"
							+ " && "
//							+ "wget http://tla.msr-inria.inria.fr/jmx2munin/jmx2munin_1.0_all.deb && "
							// Install jmx2munin into the system
							+ "dpkg -i jmx2munin_1.0_all.deb ; "
							// Force apt to download and install the
							// missing dependencies of jmx2munin without
							// user interaction
							+ "apt-get install --no-install-recommends -fy"
							+ " && "
							// Install all security relevant system packages
							+ "echo unattended-upgrades unattended-upgrades/enable_auto_updates boolean true | debconf-set-selections"
							+ " && "
							// screen is needed to allow us to re-attach
							// to the TLC process if logged in to the
							// instance directly (it's probably already
							// installed). zip is used to prepare the
							// worker tla2tools.jar (strip spec) and
							// unattended-upgrades makes sure the instance
							// is up-to-date security-wise. 
							+ "apt-get install --no-install-recommends screen zip unattended-upgrades -y"
							// Install Oracle Java8. It supports Java Mission
							// Control, an honest profiler. But first,
							// automatically accept the Oracle license because
							// installation will fail otherwise.
//							+ " && "
//							+ "echo debconf shared/accepted-oracle-license-v1-1 select true | debconf-set-selections && "
//							+ "add-apt-repository ppa:webupd8team/java -y && "
//							+ "apt-get update && "
//							+ "apt-get --no-install-recommends install oracle-java8-installer oracle-java8-set-default -y"
							// Create /mnt/tlc and change permission to be world writable
							// Requires package 'apache2' to be already installed. apache2
							// creates /var/www/html.
							// "/mnt/tlc" is on the ephemeral and thus faster storage of the
							// instance.
							+ " && "
							+ "mkdir -p /mnt/tlc/ && chmod 777 /mnt/tlc/ && "
							+ "ln -s /mnt/tlc/MC.out /var/www/html/MC.out && "
							+ "ln -s /mnt/tlc/MC.err /var/www/html/MC.err"),
					new TemplateOptions().runAsRoot(true).wrapInInitScript(
							false));			
			monitor.worked(10);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}

			// Install all security relevant system packages
			monitor.subTask("Installing security relevant system package upgrades (in background)");
			compute.runScriptOnNodesMatching(
					inGroup(groupNameUUID),
					exec("/usr/bin/unattended-upgrades"),
					new TemplateOptions().runAsRoot(true).wrapInInitScript(
							false).blockOnComplete(false).blockUntilRunning(false));
			monitor.worked(5);
			final long provision = System.currentTimeMillis();

			// Choose one of the nodes to be the master and create an
			// identifying predicate.
			final NodeMetadata master = Iterables.getLast(createNodesInGroup);

			// Copy tlatools.jar to _one_ remote host (do not exhaust upload of
			// the machine running the toolbox).
			// TODO Share the tla2tools.jar with the worker nodes by making it
			// available on the master's webserver for the clients to download.
			// On the other hand this means we are making the spec
			// world-readable. It is cloud-readable already through the RMI api.
			monitor.subTask("Copying tla2tools.jar to master node");
			SshClient sshClient = context.utils().sshForNode().apply(master);
			sshClient.put("/tmp/tla2tools.jar", jarPayLoad);
			sshClient.disconnect();
			monitor.worked(10);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}

			// Run model checker master on master
			monitor.subTask("Starting TLC model checker process on the master node (in background)");
			// The predicate will be applied to ALL instances owned by the
			// cloud account (ie AWS), even the ones in different regions
			// completely unrelated to TLC.
			final Predicate<NodeMetadata> isMaster = new Predicate<NodeMetadata>() {
				private final String masterHostname = master.getHostname();
				public boolean apply(NodeMetadata nodeMetadata) {
					// hostname can be null if instance is terminated.
					final String hostname = nodeMetadata.getHostname();
					return masterHostname.equals(hostname);
				};
			};
			compute.runScriptOnNodesMatching(
				isMaster,
				exec(" cd /mnt/tlc/ && "
						// Execute TLC (java) process inside screen
						// and shutdown on TLC's completion. But
						// detach from screen directly. Name screen 
						// session "tlc".
						// (see http://stackoverflow.com/a/10126799)
						+ "screen -dm -S tlc bash -c \" "
						// This requires a modified version where all parameters and
						// all spec modules are stored in files in a model/ folder
						// inside of the jar.
						// This is done in anticipation of other cloud providers
						// where one cannot easily pass in parameters on the command
						// line because there is no command line.
						+ "java "
							+ params.getJavaVMArgs() + " "
							// Write all tmp files to the ephemeral instance
							// storage which is expected to have a higher IOPS
							// compared to non-local storage.
							+ "-Djava.io.tmpdir=/mnt/tlc/ "
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
							// TLC tuning options
							+ params.getJavaSystemProperties() + " "
							+ "-jar /tmp/tla2tools.jar " 
							+ params.getTLCParameters() + " "
							+ "&& "
						// Let the machine power down immediately after
						// finishing model checking to cut costs. However,
						// do not shut down (hence "&&") when TLC finished
						// with an error.
						// It uses "sudo" because the script is explicitly
						// run as a user. No need to run the TLC process as
						// root.
						+ "sudo shutdown -h now"
						+ "\""), // closing opening '"' of screen/bash -c
				new TemplateOptions().runAsRoot(false).wrapInInitScript(
						true).blockOnComplete(false).blockUntilRunning(false));
			monitor.worked(5);
			final long tlcStartUp = System.currentTimeMillis();

			if (nodes > 1) {
				// copy the tla2tools.jar to the root of the master's webserver
				// to make it available to workers. However, strip the spec
				// (*.tla/*.cfg/...) from the jar file to not share the spec
				// with the world.
				monitor.subTask("Make TLC code available to all worker node(s)");
				compute.runScriptOnNodesMatching(
						isMaster,
						exec("cp /tmp/tla2tools.jar /var/www/html/tla2tools.jar && "
								+ "zip -d /var/www/html/tla2tools.jar model/*.tla model/*.cfg model/generated.properties"),
						new TemplateOptions().runAsRoot(true).wrapInInitScript(
								false));
				monitor.worked(10);
				if (monitor.isCanceled()) {
					return Status.CANCEL_STATUS;
				}
				
				// The predicate will be applied to ALL instances owned by the
				// AWS account, even the ones in different regions completely
				// unrelated to TLC.
				final Predicate<NodeMetadata> onWorkers = new Predicate<NodeMetadata>() {
					// Remove the master from the set of our nodes.
					private final Iterable<? extends NodeMetadata> workers = Iterables.filter(createNodesInGroup, new Predicate<NodeMetadata>() {
						private final String masterHostname = master.getHostname();
						public boolean apply(NodeMetadata nodeMetadata) {
							// nodeMetadata.getHostname is null for terminated hosts.
							return !masterHostname.equals(nodeMetadata.getHostname());
						};
					});
					public boolean apply(NodeMetadata nodeMetadata) {
						return Iterables.contains(workers, nodeMetadata);
					};
				};

				// see master startup for comments
				monitor.subTask("Starting TLC workers on the remaining node(s) (in background)");
				final String hostname = Iterables.getOnlyElement(master.getPrivateAddresses());
				compute.runScriptOnNodesMatching(
					onWorkers,
					exec("cd /mnt/tlc/ && "
							+ "wget http://" + hostname + "/tla2tools.jar && "
							+ "screen -dm -S tlc bash -c \" "
							+ "java "
								+ params.getJavaWorkerVMArgs() + " "
								+ "-Djava.io.tmpdir=/mnt/tlc/ "
								+ "-Dcom.sun.management.jmxremote "
								+ "-Dcom.sun.management.jmxremote.port=5400 "
								+ "-Dcom.sun.management.jmxremote.ssl=false "
								+ "-Dcom.sun.management.jmxremote.authenticate=false "
								+ params.getJavaWorkerSystemProperties() + " "
								+ "-cp /mnt/tlc/tla2tools.jar " 
								+ params.getTLCWorkerParameters() + " "
								+ hostname + " " // Use host's internal ip due to firewall reasons.
								+ "&& "
							// Terminate regardless of TLCWorker process
							// exit value. E.g. TLCWorker can terminate due
							// to a NoRouteToHostException when the master
							// shut down caused by a violation among the
							// init states.
							+ "sudo shutdown -h now"
							+ "\""), 
					new TemplateOptions().runAsRoot(false).wrapInInitScript(
							true).blockOnComplete(false).blockUntilRunning(false));
				monitor.worked(10);
			}

			// Print runtimes of various work items.
//			System.out.printf("%s spinUp\n%s provision\n%s start\n%s finish\n", (spinUp - startUp) / 1000,
//					(provision - spinUp) / 1000, (tlcStartUp - provision) / 1000,
//					(System.currentTimeMillis() - tlcStartUp) / 1000);
			
			// Communicate result to user
			monitor.done();
			final String hostname = Iterables.getOnlyElement(master.getPublicAddresses()); // master.getHostname() only returns internal name
			return new CloudStatus(
					Status.OK,
					"org.lamport.tla.toolbox.jcloud",
					Status.OK,
					String.format(
							"TLC is model checking at host %s. "
									+ "Expect to receive an email at %s with the model checking result eventually.",
							hostname,
							props.get("result.mail.address")), null, new URL(
							"http://" + hostname + "/munin/"));
		} catch (RunNodesException|IOException|RunScriptOnNodesException|NoSuchElementException|AuthorizationException e) {
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
		// Destroy all workers identified by the given group
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
}
