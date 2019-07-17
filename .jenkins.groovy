def labels = ['windows', 'master', 'macos'] // labels for Jenkins node types we will build on
def builders = [:]
for (x in labels) {
    def label = x // Need to bind the label variable before the closure - can't do 'for (label in labels)'

    // Create a map to pass in to the 'parallel' step so we can fire all the builds at once
    builders[label] = {
      node(label) {
	   stage('Preparation') { // for display purposes
	      // Get some code from a GitHub repository
	      git url: 'https://github.com/tlaplus/tlaplus.git'
	   }
	   stage('Tools') {
		withAnt(installation: 'apache ant', jdk: 'Java11') {
			if (isUnix()) {
			    sh "ant -f tlatools/customBuild.xml info compile compile-test dist test-dist"
			} else {
			    bat "ant -f tlatools\\customBuild.xml info compile compile-test dist test-dist"
			}
		}
	   }

	   stage ('RecordTestAndCoverageTools') {
	       junit 'tlatools/target/surefire-reports/onJar/*.xml'
	      // collect jacoco results for TLC
	      jacoco classPattern: 'tlatools/class', exclusionPattern: '**/*Test*.class', execPattern: 'tlatools/target/code-coverage.exec', sourcePattern: 'tlatools/src'
	   }

	   stage('Toolbox') {
	      // Run the maven build
		   if (label == 'master') {
		      wrap([$class: 'Xvnc', takeScreenshot: false, useXauthority: true]) {
			  withMaven(
			    // Maven installation declared in the Jenkins "Global Tool Configuration"
			    maven: '3.5.4',
			    jdk: 'Java11',
			    mavenLocalRepo: '.repository',
			    options: [jacocoPublisher(disabled: true)]) {

			    // Run the maven build
			    sh "mvn -Pcodesigning -U clean verify -Dmaven.test.failure.ignore=true -Dtest.skip=true"

			  } // withMaven will discover the generated Maven artifacts, JUnit Surefire & FailSafe & FindBugs reports...
		      }
	   	      // the macosx zip on the master node to have it signed with the Apple certificate on macosx.  However, only master
		      // has the lamport certificate to sign the individual toolbox bundles.
		      stash includes: 'org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-macosx.cocoa.x86_64.zip', name: 'toolbox'
                    } else {
			  withMaven(
			    // Maven installation declared in the Jenkins "Global Tool Configuration"
			    maven: '3.5.4',
			    jdk: 'Java11',
			    mavenLocalRepo: '.repository',
			    options: [jacocoPublisher(disabled: true)]) {

			    // Run the maven build
			    if (isUnix()) {
				    sh "mvn -U clean verify -Dmaven.test.failure.ignore=true -Dtest.skip=true"
			    } else {
				    bat "mvn -U clean verify -Dmaven.test.failure.ignore=true -Dtest.skip=true"
			    }

			  } // withMaven will discover the generated Maven artifacts, JUnit Surefire & FailSafe & FindBugs reports...
                    }
	   }

	   stage ('RecordTestToolbox') {
	       junit '**/target/surefire-reports/*.xml'
	   }
      }
    }
}
parallel builders

// Rest runs on master node alone

node ('master') {
	
   stage ('ReportSonarQube') {
       withSonarQubeEnv {
            withMaven(
                // Maven installation declared in the Jenkins "Global Tool Configuration"
                maven: '3.5.4',
                jdk: 'Java11') {
                sh "mvn $SONAR_MAVEN_GOAL -Dsonar.login=$SONAR_AUTH_TOKEN -Dsonar.host.url=$SONAR_HOST_URL -Dsonar.branch=master"
            }
       }
   }
   
   stage('p2Tests') {
      wrap([$class: 'Xvnc', takeScreenshot: false, useXauthority: true]) {
       sh '''
          rm -rf TLAToolbox-?.?.?-linux.gtk.x86_64.zip
		rm -rf toolbox/

		## copy currently released Toolbox and extract it (We want to make sure that we can update from it to this build)
		wget http://dl.tlapl.us/tlatoolbox/products/TLAToolbox-1.6.0-linux.gtk.x86_64.zip
		unzip -qq TLAToolbox*.zip

		cd toolbox/
		
		## Update current Toolbox release to this version
		./toolbox -nosplash -application org.eclipse.equinox.p2.director \
		-repository file://${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/repository \
		-uninstallIU org.lamport.tla.toolbox.product.product \
		-installIU org.lamport.tla.toolbox.product.product \
		-profileProperties org.eclipse.update.install.features=true

		## Use Toolbox's p2 director to install the test feature into the previuos toolbox release to verify the update above worked and didn't trash anything.
		./toolbox -nosplash -application org.eclipse.equinox.p2.director \
		-repository file://${WORKSPACE}/org.lamport.tla.toolbox.p2repository/target/repository/ \
		-installIU org.lamport.tla.toolbox.feature.uitest.feature.group

		## Run the SWTBot smoke tests to check product zips
		./toolbox -nosplash -application org.eclipse.swtbot.eclipse.junit.headless.swtbottestapplication \
		-testApplication org.lamport.tla.toolbox.application \
		-product org.lamport.tla.toolbox.product.standalone.product \
		-nouithread \
		-testPluginName org.lamport.tla.toolbox.tool.tlc.ui.uitest \
		formatter=org.apache.tools.ant.taskdefs.optional.junit.PlainJUnitResultFormatter \
		formatter=org.apache.tools.ant.taskdefs.optional.junit.XMLJUnitResultFormatter,org.lamport.tla.toolbox.tool.tlc.ui.uitest.SmokeTests.xml \
		-className org.lamport.tla.toolbox.SmokeTests \
		-data workspace$(date +%s) \
		-clean

		cp *.xml ${WORKSPACE}/
       '''
      }
   }

   stage ('RecordTestP2UpdateManager') {
       // Collect junit output for p2 smoke tests
       junit 'toolbox/org.lamport.tla.toolbox.tool.tlc.ui.uitest.SmokeTests.xml'
   }
   
   stage('CreateRPMFile') {
       sh '''
        cd org.lamport.tla.toolbox.product.product/target/
        fakeroot alien --to-rpm --scripts TLAToolbox-?.?.?-linux.gtk.amd64.deb
        cp TLA*.rpm products/
       '''
   }
   
   stage('CreateAPTRepo') {
       sh '''
        chmod -x org.lamport.tla.toolbox.product.product/createAptRepo.sh
        cp org.lamport.tla.toolbox.product.product/target/*.deb org.lamport.tla.toolbox.product.product/target/repository/
        cd org.lamport.tla.toolbox.product.product/target/repository/
        bash -x ../../createAptRepo.sh .
       '''
   }
   
   stage('RenderChangelog') { // Render the github flavord markdown to html
       sh 'grip --context=tlaplus/tlaplus --export ${WORKSPACE}/general/docs/changelogs/ch1_6_1.md ${WORKSPACE}/general/docs/changelogs/changelog.html'
   }
}

node ('macos') {
    stage('SignToolbox') {
        sh 'rm -rf *'
        unstash 'toolbox'
        sh 'ls -lah'
        sh 'unzip org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-macosx.cocoa.x86_64.zip'
        sh 'codesign -f -s "Developer ID Application: M K (3PCM4M3RWK)" -v "TLA+ Toolbox.app" --deep'
        sh 'ditto -ck --sequesterRsrc --keepParent "TLA+ Toolbox.app" TLAToolbox-1.6.1-macosx.cocoa.x86_64.zip'
        sh 'mv TLAToolbox-1.6.1-macosx.cocoa.x86_64.zip org.lamport.tla.toolbox.product.product/target/products/'
        stash includes: 'org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-macosx.cocoa.x86_64.zip', name: 'signed'
    }
}

node ('master') {
   stage('Archive') {
      unstash 'signed'
      fingerprint '**/org.lamport.tla.toolbox.product.product/target/repository/, **/org.lamport.tla.toolbox.product.product/target/products/*.zip, **/org.lamport.tla.toolbox.product.product/target/products/*.deb, **/tlatools/dist/, **/org.lamport.tla.toolbox.doc/html/'

      archiveArtifacts '**/general/docs/changelogs/changelog.html, **/org.lamport.tla.toolbox.product.product/target/org.lamport.tla.toolbox.product.product-1.4.0-SNAPSHOT.zip, **/org.lamport.tla.toolbox.p2repository/target/repository/, **/org.lamport.tla.toolbox.product.product/target/repository/, **/org.lamport.tla.toolbox.product.product/target/products/*.zip, **/org.lamport.tla.toolbox.product.product/target/products/*.deb, **/org.lamport.tla.toolbox.product.product/target/products/*.rpm, **/org.lamport.tla.toolbox.product.product/target/products/32bit_x86/*, **/tlatools/dist/, **/org.lamport.tla.toolbox.doc/html/'
   }
}

node ('master') {
   stage ('DraftGithubRelease') {
	if (env.JOB_NAME == 'Release-HEAD-master-Toolbox') {
         sh '''
           #!/bin/bash

           cd ${WORKSPACE}/general/docs/changelogs

           ## Append sha1 sum to changelog (last line of changelog has the table header).
           sha1sum ${WORKSPACE}/tlatools/dist/tla2tools.jar | sed -r 's/  /|/g' >> ch1_6_1.md
           sha1sum ${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-win32.win32.x86_64.zip | sed -r 's/  /|/g' >> ch1_6_1.md
           sha1sum ${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-macosx.cocoa.x86_64.zip | sed -r 's/  /|/g' >> ch1_6_1.md     
           sha1sum ${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-linux.gtk.x86_64.zip | sed -r 's/  /|/g' >> ch1_6_1.md
           
           ## Two above as one-liner without intermediate file.
           $(jq -n --argjson changelog "$(cat ch1_6_1.md | jq  --raw-input --slurp .)" -f gh-1_6_1.jq > gh-1_6_1.json)

           ## Get id of existing draft release with given name.
           DRAFT_RELEASE=$(curl -sS -H "Authorization: token ${GITHUB_TOKEN}" https://api.github.com/repos/tlaplus/tlaplus/releases --header "Content-Type: application/json" | jq '.[]| select(.draft==true and .name=="The Aristotle release") | .id')
           echo $DRAFT_RELEASE

           ## Update draft release with latest changelog in case it changed.
           ## https://developer.github.com/v3/repos/releases/#edit-a-release
           curl -sS -H "Authorization: token ${GITHUB_TOKEN}" https://api.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE -d @gh-1_6_1.json -X PATCH --header "Content-Type: application/json"

           ## Remove old assets otherwise upload below will error.
           ASSETS=$(curl -sS -H "Authorization: token ${GITHUB_TOKEN}" https://api.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets --header "Content-Type: application/json" | jq '.[]| .id')
           for id in $(echo "$ASSETS"); do
              ## DELETE /repos/:owner/:repo/releases/assets/:asset_id
              curl -sS -X DELETE -H "Authorization: token ${GITHUB_TOKEN}" https://api.github.com/repos/tlaplus/tlaplus/releases/assets/$id
           done
           
            ## p2 repository
            #curl -s -X POST -H "Content-Type: application/zip" -H "Authorization: token ${GITHUB_TOKEN}" https://uploads.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets?name=repository.zip --upload-file ${WORKSPACE}/org.lamport.tla.toolbox.p2repository/target/repository/repository.zip
            ## tla2tools.jar
            curl -s -X POST -H "Content-Type: application/zip" -H "Authorization: token ${GITHUB_TOKEN}" https://uploads.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets?name=tla2tools.jar --upload-file ${WORKSPACE}/tlatools/dist/tla2tools.jar
            ## macOS
            curl -s -X POST -H "Content-Type: application/zip" -H "Authorization: token ${GITHUB_TOKEN}" https://uploads.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets?name=TLAToolbox-1.6.1-macosx.cocoa.x86_64.zip --upload-file ${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-macosx.cocoa.x86_64.zip
            ## win32
            curl -s -X POST -H "Content-Type: application/zip" -H "Authorization: token ${GITHUB_TOKEN}" https://uploads.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets?name=TLAToolbox-1.6.1-win32.win32.x86_64.zip --upload-file ${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-win32.win32.x86_64.zip
            ## Linux
            curl -s -X POST -H "Content-Type: application/zip" -H "Authorization: token ${GITHUB_TOKEN}" https://uploads.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets?name=TLAToolbox-1.6.1-linux.gtk.x86_64.zip --upload-file ${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/products/TLAToolbox-1.6.1-linux.gtk.x86_64.zip
            ## deb
            #curl -s -X POST -H "Content-Type: application/zip" -H "Authorization: token ${GITHUB_TOKEN}" https://uploads.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets?name=TLAToolbox-1.6.1-linux.gtk.amd64.deb --upload-file ${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/repository/TLAToolbox-1.6.1-linux.gtk.amd64.deb
            ## RPM
            #curl -s -X POST -H "Content-Type: application/zip" -H "Authorization: token ${GITHUB_TOKEN}" https://uploads.github.com/repos/tlaplus/tlaplus/releases/$DRAFT_RELEASE/assets?name=TLAToolbox-1.6.1-linux.gtk.amd64.rpm --upload-file ${WORKSPACE}/org.lamport.tla.toolbox.product.product/target/products/TLA\\+Toolbox-1.6.1~*.x86_64.rpm
         '''
        }
   }
}



