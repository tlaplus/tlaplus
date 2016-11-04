Eclipse Oomph is a tool to simplify and automate the setup of Eclipse development environments. In this case, it creates a development environment for the TLA+Tools (TLC, SANY, ...) and the Eclipse-based TLA+Toolbox. In order to use the TLA.setup script in this folder, one has to:

[A screencast is available that captures the written instructions below.](https://vimeo.com/190224035)

0. Requires a recent - at the time of writing this is 1.8 - JDK (Java Development Environment)
1. Install the Oomph Eclipse installer from https://wiki.eclipse.org/Eclipse_Installer
2. Start the downloaded Oomph installer
3. Switch to "Advanced Mode" by clicking the button in the right upper corner depicted with three horizontal lines
4. Select "Eclipse Platform" on the Product list (expand "Eclipse.org" node)
  1. Choose "Neon" as the product version at the bottom ![Chose Platform](https://raw.githubusercontent.com/lemmy/tlaplus/master/general/ide/images/00_PlatformSelection.png)
5. On the next screen, expand "Github Project" in the tree and select the check-box left to "TLA+" 
  1. Verify that "TLA+" shows up under "Project" at the bottom table and that the "Master" stream is selected ![Chose Project](https://raw.githubusercontent.com/lemmy/tlaplus/master/general/ide/images/01_ProjectSelection.png)
6. On the next page, select whether to use anonymous Github access (read-only) from the "TLA+ Github Repository" dropdown list ![Chose anonymous access](https://raw.githubusercontent.com/lemmy/tlaplus/master/general/ide/images/02_Variables.png)
  1. Most users will want to chose read-only access.
  2. If you know that you have write access to the tlaplus/tlaplus Github repository, make sure you:
     1. [Generate an SSH key](https://help.github.com/articles/generating-an-ssh-key/)
     2. [Uploaded your public SSH key (id_rsa.pub or id_dsa.pub) to Github](https://github.com/settings/keys) (Settings > SSH and GPG keys > New SSH key)
7. Hit Finish and have a coffee or tea (though you might have to accept a license dialog...)
8. After a few minutes, the Eclipse IDE will start up. At this point, the workspace will be empty. Click the spinning arrows to open the progress dialog. ![Status](https://raw.githubusercontent.com/lemmy/tlaplus/master/general/ide/images/03_Status.png)
9. Check the progress dialog for any errors. ![Progress](https://raw.githubusercontent.com/lemmy/tlaplus/master/general/ide/images/04_Progress.png)
  1. If you opted for write access in 6. and the dialog shows an "auth failure" when it tries to clone the git repository, it is likely that Eclipse uses the wrong SSH key. In Eclipse, go to Window > Preferences > General > Network Connections > SSH2 and make sure the path in "SSH2 Home" is correct and restart the setup task via Windows > Perform Setup Task.
     ![SSH Key](https://raw.githubusercontent.com/lemmy/tlaplus/master/general/ide/images/05_SSHKey.png)
10. You are now set to start the TLAToolbox from within Eclipse:
  1. In Eclipse, open the file org.lamport.tla.toolbox.product.product/org.lamport.tla.toolbox.product.product.product
  2. Hit on the green launch arrow in the right upper corner of the Product editor. ![TLAToolbox](https://raw.githubusercontent.com/lemmy/tlaplus/master/general/ide/images/06_Toolbox.png)

