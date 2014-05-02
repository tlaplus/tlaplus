Simply run:

mvn clean verify
mkdir -p target/source/features/org.apache.jclouds.feature/
mvn verify

The feature.xml has been create inside Eclipse (new feature project) and all jclouds bundles manually added to it. The "Version" button in the feature 
editor syncs the bundle version into the feature.xml.

Make sure to start these jclouds bundles explicitly in the launch config to activate OSGi. Otherwise expect NoClassDefFoundExceptions:

* aws-ec2_1.7.2
* com.jcraft.jsch.agentproxy.connector-factory_0.0.7
* ec2_1.7.2
* jclouds-core_1.7.2
* sts_1.7.2

(* org.lamport.tla.toolbox.jclouds)