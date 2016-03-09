Eclipse Oomph is a tool to simplify and automate the setup of Eclipse development environments. In this case, it creates a development environment for the TLA+Tools (TLC, SANY, ...) and the Eclipse-based TLA+Toolbox. In order to use the TLA.setup script in this folder, one has to:

0. Requires a recent - at the time of writing this is 1.8 - JDK (Java Development Environment)
1. Install the Oomph Eclipse installer from https://wiki.eclipse.org/Eclipse_Installer
2. Start the downloaded Oomph installer
3. Switch to "Advanced Mode" by clicking the button in the right upper corner depicted with three horizontal lines
4. Select "Eclipse Platform" on the Product list (expand "Eclipse.org" node)
  1. Choose "Mars" as the product version at the bottom
5. On the next screen, click the green "+" sign at the upper right corner
  1. Select "Github Project" as the Category
  2. As "Resource URI" add 'https://raw.githubusercontent.com/tlaplus/tlaplus/master/general/ide/TLA.setup'
  3. Double click newly created "TLA+" item
  4. Make sure "<User>- TLA+" shows up under "Project" at the bottom table
6. On the next page, select whether to use anonymous access to github or not from the "TLA+ Github Repository" dropdown list
7. Hit Finish and have a coffee or tea (though you might have to accept a license dialog...)

