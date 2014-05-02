package org.lamport.tla.toolbox.jcloud;

import static com.google.common.base.Predicates.not;
import static com.google.common.collect.Iterables.concat;
import static com.google.common.collect.Iterables.getOnlyElement;
import static org.jclouds.compute.options.TemplateOptions.Builder.runScript;
import static org.jclouds.compute.predicates.NodePredicates.TERMINATED;
import static org.jclouds.compute.predicates.NodePredicates.inGroup;
import static org.jclouds.scriptbuilder.domain.Statements.exec;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

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
import org.jclouds.enterprise.config.EnterpriseConfigurationModule;
import org.jclouds.io.Payload;
import org.jclouds.logging.slf4j.config.SLF4JLoggingModule;
import org.jclouds.scriptbuilder.domain.Statement;
import org.jclouds.scriptbuilder.statements.java.InstallJDK;
import org.jclouds.scriptbuilder.statements.login.AdminAccess;
import org.jclouds.ssh.SshClient;
import org.jclouds.sshj.config.SshjSshClientModule;

import com.google.common.base.Predicates;
import com.google.common.collect.ImmutableSet;
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

	public CloudDistributedTLCJob(String aName) {
		super(aName);
		groupName = aName;
		// TODO read from launch
		modelPath = Paths.get("/home/markus/src/TLA/models/Grid5kPerformanceTest/Test.toolbox/k8l8n6");
		mainClass = "tlc2.tool.distributed.TLCServer";
		imageId = US_EAST_UBUNTU_14_04_AMD64;
		ownerId = OWNER_ID_CANONICAL_LTD;
	}

	private final String ownerId;
	private final String imageId;
	private final Path modelPath;
	private final String cloudProvider = "aws-ec2";
	private final String groupName;
	private final int workers = 1;
	private final String mainClass;

	// public CloudDistributedTLCJob(String specName, String modelName,
	// ILaunch launch, int workers, String cloudProvider) {
	// super(specName, modelName, launch, workers);
	// this.cloudProvider = cloudProvider;
	// }

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.lamport.tla.toolbox.tool.tlc.job.TLCJob#run(org.eclipse.core.runtime
	 * .IProgressMonitor)
	 */
	@Override
	protected IStatus run(IProgressMonitor monitor) {
		
		ComputeServiceContext context = null;
		try {
			final Payload jarPayLoad = PayloadHelper.appendModel2Jar(modelPath, mainClass, monitor);

			// example of specific properties, in this case optimizing image
			// list to
			// only amazon supplied
			final Properties properties = new Properties();
			properties
			.setProperty(
					AWSEC2Constants.PROPERTY_EC2_AMI_QUERY,
					ownerId);
//			properties.setProperty(AWSEC2Constants.PROPERTY_EC2_CC_REGIONS, "eu-west-1");

			// example of injecting a ssh implementation
			final Iterable<AbstractModule> modules = ImmutableSet
					.<AbstractModule> of(new SshjSshClientModule(),
							new SLF4JLoggingModule(),
							new EnterpriseConfigurationModule());

			final ContextBuilder builder = ContextBuilder
					.newBuilder(cloudProvider)
					.credentials(identity, credential).modules(modules)
					.overrides(properties);

			System.out.printf(">> initializing %s%n", builder.getApiMetadata());

			context = builder.buildView(ComputeServiceContext.class);
			final ComputeService compute = context.getComputeService();

			// start a node
            TemplateBuilder templateBuilder = compute.templateBuilder();
            templateBuilder.imageId(imageId);

            // note this will create a user with the same name as you on the
            // node. ex. you can connect via ssh publicip
            Statement bootInstructions = AdminAccess.standard();
            templateBuilder.options(runScript(bootInstructions));

            Set<? extends NodeMetadata> createNodesInGroup;
				createNodesInGroup = compute.createNodesInGroup(groupName, workers , templateBuilder.build());

            NodeMetadata node = getOnlyElement(createNodesInGroup);
            System.out.printf("<< node %s: %s%n", node.getId(),
                  concat(node.getPrivateAddresses(), node.getPublicAddresses()));

            // Install Java
            Statement installOpenJDK = InstallJDK.fromOpenJDK();
			Map<? extends NodeMetadata, ExecResponse> responses = compute
					.runScriptOnNodesMatching(
							inGroup(groupName),
							installOpenJDK);
			
			// Create /mnt/tlc and change permission to be world writable
			responses = compute.runScriptOnNodesMatching(
					inGroup(groupName),
					exec("mkdir /mnt/tlc/ && chmod 777 /mnt/tlc/"),
					new TemplateOptions().runAsRoot(true).wrapInInitScript(
							false));			
            
			// Copy tlatools.jar to remote host
			SshClient sshClient = context.utils().sshForNode().apply(node);
			
			sshClient.put("/mnt/tlc/tla2tools.jar",
					jarPayLoad);
			
			sshClient.disconnect();
			
			// Run model checker master
			responses = compute.runScriptOnNodesMatching(
					inGroup(groupName),
					exec("cd /mnt/tlc/ && java -jar /mnt/tlc/tla2tools.jar"),
					new TemplateOptions().runAsRoot(false).wrapInInitScript(
							false));

			for (Entry<? extends NodeMetadata, ExecResponse> response : responses
					.entrySet()) {
				System.out.printf(
						"<< node %s: %s%n",
						response.getKey().getId(),
						concat(response.getKey().getPrivateAddresses(),
								response.getKey().getPublicAddresses()));
				System.out.printf("<<     %s%n", response.getValue());
			}
            
			return Status.OK_STATUS;
		} catch (RunNodesException e) {
			e.printStackTrace();
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					e.getMessage(), e);
		} catch (IOException e) {
			e.printStackTrace();
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					e.getMessage(), e);
		} catch (RunScriptOnNodesException e) {
			e.printStackTrace();
			return new Status(Status.ERROR, "org.lamport.tla.toolbox.jcloud",
					e.getMessage(), e);
		} finally {
			if (context != null) {
				// Destroy all workers identified by the group
				ComputeService computeService = context.getComputeService();
				if (computeService != null) {
					Set<? extends NodeMetadata> destroyed = computeService
							.destroyNodesMatching(
									Predicates.<NodeMetadata> and(not(TERMINATED),
											inGroup(groupName)));
					System.out.printf("<< destroyed nodes %s%n", destroyed);
				}
				context.close();
			}
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
