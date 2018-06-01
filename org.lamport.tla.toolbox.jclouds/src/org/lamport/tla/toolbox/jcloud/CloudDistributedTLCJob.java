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
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Properties;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.jclouds.ContextBuilder;
import org.jclouds.compute.ComputeService;
import org.jclouds.compute.ComputeServiceContext;
import org.jclouds.compute.RunNodesException;
import org.jclouds.compute.RunScriptOnNodesException;
import org.jclouds.compute.domain.ExecChannel;
import org.jclouds.compute.domain.ExecResponse;
import org.jclouds.compute.domain.NodeMetadata;
import org.jclouds.compute.domain.TemplateBuilder;
import org.jclouds.compute.options.TemplateOptions;
import org.jclouds.io.Payload;
import org.jclouds.logging.config.ConsoleLoggingModule;
import org.jclouds.logging.slf4j.config.SLF4JLoggingModule;
import org.jclouds.rest.AuthorizationException;
import org.jclouds.scriptbuilder.statements.login.AdminAccess;
import org.jclouds.ssh.SshClient;
import org.jclouds.ssh.SshException;
import org.jclouds.sshj.config.SshjSshClientModule;
import org.lamport.tla.toolbox.tool.tlc.job.ITLCJobStatus;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJobFactory;

import com.google.common.base.Predicate;
import com.google.common.base.Predicates;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.io.ByteStreams;
import com.google.inject.AbstractModule;

/*
 * TODO
 * ====
 * - Reverse PTR records in DNS to make it less likely that emails coming out of the VM are classified as SPAM
 * -- Azure has only support for it in its service API but not in JClouds
 * --- Also see https://docs.microsoft.com/en-us/azure/dns/dns-reverse-dns-for-azure-services
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
	private boolean isCLI = false;
	private boolean doJfr = false;

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
		monitor.beginTask("Starting TLC model checker in the cloud", 85 + (nodes > 1 ? 20 : 0));
		// Validate credentials and fail fast if null or syntactically incorrect
		if (!params.validateCredentials().equals(Status.OK_STATUS)) {
			return params.validateCredentials();
		}
		
		ComputeServiceContext context = null;
		try {
			// Tweak tla2tools in a background thread. It takes a couple of seconds to run
			// pack200 to shrink the files size but we can lookup or launch a cloud instance
			// in the meantime.
			monitor.subTask("Tweaking tla2tools.jar to contain the spec & model (in background)");	
			final ExecutorService executor = Executors.newSingleThreadExecutor();
			final Future<Payload> future = executor.submit(() -> {
				return PayloadHelper
						.appendModel2Jar(modelPath,
								props.getProperty(TLCJobFactory.MAIN_CLASS), props,
								monitor);
			});
			executor.shutdown();
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
			final Iterable<AbstractModule> modules = ImmutableSet.<AbstractModule>of(new SshjSshClientModule(),
					isCLI ? new ConsoleLoggingModule() : new SLF4JLoggingModule());

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

			final Set<? extends NodeMetadata> createNodesInGroup = provisionNodes(compute, monitor);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}

			// Choose one of the nodes to be the master and create an
			// identifying predicate.
			final NodeMetadata master = Iterables.getLast(createNodesInGroup);
			final String hostname = Iterables.getOnlyElement(master.getPublicAddresses()); // master.getHostname() only returns internal name

			// Copy tlatools.jar to _one_ remote host (do not exhaust upload of
			// the machine running the toolbox).
			// TODO Share the tla2tools.jar with the worker nodes by making it
			// available on the master's webserver for the clients to download.
			// On the other hand this means we are making the spec
			// world-readable. It is cloud-readable already through the RMI api.
			monitor.subTask("Copying tla2tools.jar to master node at " + hostname);
			SshClient sshClient = context.utils().sshForNode().apply(master);
			sshClient.put("/tmp/tla2tools.pack.gz", future.get());
			monitor.worked(10);
			if (monitor.isCanceled()) {
				return Status.CANCEL_STATUS;
			}

			final String tlcMasterCommand = " shutdown -c && rm -rf /mnt/tlc/* && " // Cancel and remove any pending shutdown and leftovers from previous runs.
					+ "cd /mnt/tlc/ && "
					// Decompress tla2tools.pack.gz
					+ "unpack200 /tmp/tla2tools.pack.gz /tmp/tla2tools.jar"
					+ " && "
					// Execute TLC (java) process inside screen
					// and shutdown on TLC's completion. But
					// detach from screen directly. Name screen 
					// session "tlc".
					// (see http://stackoverflow.com/a/10126799)
					+ (isCLI ? "" : "screen -dm -S tlc bash -c \" ")
					// This requires a modified version where all parameters and
					// all spec modules are stored in files in a model/ folder
					// inside of the jar.
					// This is done in anticipation of other cloud providers
					// where one cannot easily pass in parameters on the command
					// line because there is no command line.
					+ "java "
						+ params.getJavaVMArgs() + " "
						+ (doJfr ? params.getFlightRecording() + " " : "")
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
						+ (isCLI ? "|& tee /mnt/tlc/MC.out " : "")
						+ "&& "
					// Run any cloud specific cleanup tasks.
					// When CloudDistributedTLCJob runs in synchronous CLI mode (isCLI), it will destroy
					// the VMs (nodes) via the jclouds API. No need to deallocate nodes
					// via special logic.
					+ (isCLI ? "/bin/true" : params.getCloudAPIShutdown())
					+ " && "
					// Let the machine power down immediately after
					// finishing model checking to cut costs. However,
					// do not shut down (hence "&&") when TLC finished
					// with an error.
					// It uses "sudo" because the script is explicitly
					// run as a user. No need to run the TLC process as
					// root.
					+ "sudo shutdown -h " + (isCLI ? "+10" : "now")
					+ (isCLI ? "" : "\""); // closing opening '"' of screen/bash -c
			if (isCLI) {
				monitor.subTask("Starting TLC model checker process");
				// Execute command via ssh instead of as a script to get access to the TLC
				// processes' stdout and stderr.
				//TODO Better handle error case.
				ExecChannel channel = sshClient.execChannel(tlcMasterCommand);
				// Send remote TLC's stdout to local stdout (this throws a TransportException
				// unless shutdown is postponed by a few minutes above).
				ByteStreams.copy(channel.getOutput(), System.out);
				if (doJfr) {
					// Get Java Flight Recording from remote machine and save if to a local file in
					// the current working directory. We call "cat" because sftclient#get fails with
					// the old net.schmizz.sshj and an update to the newer com.hierynomus seems 
					// awful lot of work.
					channel = sshClient.execChannel("cat /mnt/tlc/tlc.jfr");
					final InputStream output = channel.getOutput();
					final String cwd = Paths.get(".").toAbsolutePath().normalize().toString() + File.separator;
					final File jfr = new File(cwd + "tlc.jfr");
					ByteStreams.copy(output, new FileOutputStream(jfr));
					if (jfr.length() == 0) {
						System.err.println("Received empty Java Flight recording. Not creating tlc.jfr file");
						jfr.delete();
					}
				}
				// Finally close the ssh connection.
				sshClient.disconnect();
				monitor.subTask("TLC model checker process finished");
				// Eagerly destroy the instance after we pulled the tlc.jfr file from it. No
				// point in waiting for shutdown -h +10 to shutdown the instance.
				destroyNodes(context, groupNameUUID);
			} else {
				sshClient.disconnect();

				// Run model checker master on master
				monitor.subTask("Starting TLC model checker process on the master node (in background)");
				final ExecResponse response = compute.runScriptOnNode(master.getId(), exec(tlcMasterCommand),
						new TemplateOptions().overrideLoginCredentials(master.getCredentials()).runAsRoot(false)
								.wrapInInitScript(true).blockOnComplete(false).blockUntilRunning(false));
				throwExceptionOnErrorResponse(master, response, "Starting TLC model checker process on the master node");
				monitor.worked(5);

				if (nodes > 1) {
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
					// copy the tla2tools.jar to the root of the master's webserver
					// to make it available to workers. However, strip the spec
					// (*.tla/*.cfg/...) from the jar file to not share the spec
					// with the world.
					monitor.subTask("Make TLC code available to all worker node(s)");
					Map<? extends NodeMetadata, ExecResponse> execResponse = compute.runScriptOnNodesMatching(
							isMaster,
							exec("cp /tmp/tla2tools.jar /var/www/html/tla2tools.jar && "
									+ "zip -d /var/www/html/tla2tools.jar model/*.tla model/*.cfg model/generated.properties"),
							new TemplateOptions().runAsRoot(true).wrapInInitScript(
									false));
					throwExceptionOnErrorResponse(execResponse, "Make TLC code available to all worker node");
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
					final String privateHostname = Iterables.getOnlyElement(master.getPrivateAddresses());
					execResponse = compute.runScriptOnNodesMatching(
						onWorkers,
						exec("cd /mnt/tlc/ && "
								+ "wget http://" + privateHostname + "/tla2tools.jar && "
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
									+ privateHostname + " " // Use host's internal ip due to firewall reasons.
									+ "&& "
								// Terminate regardless of TLCWorker process
								// exit value. E.g. TLCWorker can terminate due
								// to a NoRouteToHostException when the master
								// shut down caused by a violation among the
								// init states.
					            // Run any cloud specific cleanup tasks.
					            + params.getCloudAPIShutdown()
					            + " && "
								+ "sudo shutdown -h now"
								+ "\""), 
						new TemplateOptions().runAsRoot(false).wrapInInitScript(
								true).blockOnComplete(false).blockUntilRunning(false));
					throwExceptionOnErrorResponse(execResponse, "Starting TLC workers");
					monitor.worked(10);
				}
				
			}

			// Communicate result to user
			monitor.done();
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
		} catch (ExecutionException|InterruptedException|RunNodesException|IOException|RunScriptOnNodesException|NoSuchElementException|AuthorizationException|SshException e) {
			e.printStackTrace();
			if (context != null) {
				destroyNodes(context, groupNameUUID);
			}
			// signal error to caller
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					e.getMessage(), e);
		} catch (ScriptException e) {
			if (context != null) {
				destroyNodes(context, groupNameUUID);
			}
			// signal error to caller
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					e.getTitle(), e);
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

	private Set<? extends NodeMetadata> provisionNodes(ComputeService compute, IProgressMonitor monitor)
			throws RunNodesException, RunScriptOnNodesException {

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
			if (isCLI) {
				templateOptions.tags(Arrays.asList("CLI"));
			}

            final TemplateBuilder templateBuilder = compute.templateBuilder();
            templateBuilder.options(templateOptions);
            templateBuilder.imageId(params.getImageId());
            templateBuilder.hardwareId(params.getHardwareId());

            // Everything configured, now launch node
			monitor.subTask(String.format("Starting %s %s instance%s in region %s.", nodes > 1 ? nodes : "a",
					params.getHardwareId(), nodes > 1 ? "s" : "", params.getRegion()));
			final Set<? extends NodeMetadata> createNodesInGroup = compute.createNodesInGroup(groupNameUUID,
					nodes, templateBuilder.build());
			monitor.worked(20);
			if (monitor.isCanceled()) {
				return createNodesInGroup;
			}

			// Install custom tailored jmx2munin to monitor the TLC process. Can
			// either monitor standalone tlc2.TLC or TLCServer.
			monitor.subTask("Provisioning TLC environment on all node(s)");
			final String email = props.getProperty(TLCJobFactory.MAIL_ADDRESS);
			Map<? extends NodeMetadata, ExecResponse> execResponse = compute.runScriptOnNodesMatching(
					inGroup(groupNameUUID),
					// Creating an entry in /etc/alias that makes sure system email sent
					// to root ends up at the address given by the user. Note that this
					// has to be done before postfix gets installed later. postfix
					// re-generates the aliases file for us.
					exec(	"echo root: " + email + " >> /etc/aliases"
							+ " && "
							// OS tuning parameters for (distributed) TLC:
							// - Disable hugepage defragmentation (especially important on highmem instances)
							+ "echo never > /sys/kernel/mm/transparent_hugepage/defrag"
							+ " && "
							// - Turn off NUMA balancing
							+ "echo 0 > /proc/sys/kernel/numa_balancing"
							+ " && "
                            // Don't want dpkg to require user interaction.
							+ "export DEBIAN_FRONTEND=noninteractive"
							+ " && "
							+ params.getHostnameSetup()
							+ " && "
							// Oracle Java 8
							+ "add-apt-repository ppa:webupd8team/java -y && "
							// Accept license before apt (dpkg) tries to present it to us (which fails due to 'noninteractive' mode below)
							// see http://stackoverflow.com/a/19391042
							+ "echo debconf shared/accepted-oracle-license-v1-1 select true | sudo debconf-set-selections && "
							+ "echo debconf shared/accepted-oracle-license-v1-1 seen true | sudo debconf-set-selections && "
							+ params.getExtraRepositories()
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
							+ "wget https://github.com/lemmy/jmx2munin/raw/df6ce053a6d178e7a70434ab2f91089acadf0525/jmx2munin_1.0_all.deb"
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
							+ "apt-get install --no-install-recommends mdadm e2fsprogs screen zip unattended-upgrades oracle-java8-installer oracle-java8-set-default "
									+ params.getExtraPackages() + " -y"
							+ " && "
							// Delegate file system tuning to cloud specific code.
							+ params.getOSFilesystemTuning()
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
							+ "ln -s /mnt/tlc/MC.out /var/www/html/MC.txt && " // Microsoft IE and Edge fail to show line breaks correctly unless ".txt" extension.
							+ "ln -s /mnt/tlc/MC.err /var/www/html/MC.err && "
							+ "ln -s /mnt/tlc/tlc.jfr /var/www/html/tlc.jfr"),
					new TemplateOptions().runAsRoot(true).wrapInInitScript(
							false));			
			throwExceptionOnErrorResponse(execResponse, "Provisioning TLC environment on all nodes");
			monitor.worked(10);
			if (monitor.isCanceled()) {
				return createNodesInGroup;
			}

			// Install all security relevant system packages
			monitor.subTask("Installing security relevant system package upgrades (in background)");
			execResponse = compute.runScriptOnNodesMatching(
					inGroup(groupNameUUID),
					exec("screen -dm -S security bash -c \"/usr/bin/unattended-upgrades\""),
					new TemplateOptions().runAsRoot(true).wrapInInitScript(
							true).blockOnComplete(false).blockUntilRunning(false));
			throwExceptionOnErrorResponse(execResponse, "Installing security relevant system package upgrades");
			monitor.worked(5);
			
			return createNodesInGroup;
	}

	private void throwExceptionOnErrorResponse(final Map<? extends NodeMetadata, ExecResponse> execResponse, final String step) {
		execResponse.forEach((node, exec) -> {
			// If the script above failed on any number of nodes for whatever reason, don't
			// continue but destroy all nodes.
			if (exec.getExitStatus() > 0) {
				throw new ScriptException(node, exec, step);
			}
		});
	}

	private void throwExceptionOnErrorResponse(final NodeMetadata node, final ExecResponse execResponse, final String step) {
			// If the script above failed on any number of nodes for whatever reason, don't
			// continue but destroy all nodes.
			if (execResponse.getExitStatus() > 0) {
				throw new ScriptException(node, execResponse, step);
			}
	}
	
	public void setIsCLI(boolean cli) {
		this.isCLI = cli;
	}
	
	public void setDoJfr(boolean doIt) {
		this.doJfr = doIt;
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
	
	@SuppressWarnings("serial")
	class ScriptException extends RuntimeException {

		private final String title;

		public ScriptException(final NodeMetadata node, final ExecResponse exec, final String step) {
			super(exec.getOutput());
			this.title = String.format(
					"Launching TLC on %s unsuccessful.\nStep '%s' failed on node '%s'.",
					params.getCloudProvider(), step, node.getName());
		}

		public String getTitle() {
			return title;
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
