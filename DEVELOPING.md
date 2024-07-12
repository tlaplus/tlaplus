Overview
--------
This file summarizes basic development knowledge & practices for this project.
You will learn the repository structure, how to build & test the software it contains from your command line interface (CLI), how to set up your interactive development environment (IDE), and several other tidbits.
This project is written entirely in Java.

Repository Layout
-----------------
Here is a diagram of the repository layout.
There are other files and directories beyond these, but these are the most important:
```
/
├── LICENSE                     # The project license
├── README.md                   # Basic info about the project
├── CONTRIBUTING.md             # Info on contributing to the project
├── DEVELOPING.md               # This document
├── pom.xml                     # The Maven build system definition file
├── toolbox/                    # All files related to the TLA⁺ Toolbox IDE
├── tlatools/
│   └── org.lamport.tlatools/   # All files related to the TLA⁺ Tools
│       ├── .classpath          # The Eclipse IDE classpath file
│       ├── .project            # The Eclipse IDE project file
│       ├── customBuild.xml     # The Ant build system definition file
│       ├── pom.xml             # A Maven build file wrapping the Ant file
│       ├── src/                # The TLA⁺ Tools source code dir
│       ├── test/               # Unit tests for the TLA⁺ Tools
│       ├── test-model/         # TLA⁺ modules and models for use in tests
│       ├── lib/                # Vendored dependencies; checked-in jar files
│       └── javacc/             # Source files for the TLA⁺ parser generator
└───.github/
    ├── CODE_OF_CONDUCT.md      # The code of conduct
    └── workflows/              # GitHub CI workflow definition files
        ├── pr.yml              # The CI workflow that validates PRs
        └── main.yml            # Build & publish master branch to pre-release
```

Build & Test TLA⁺ Tools
----------------------
Install the following dependencies to your path:
 * [Java Development Kit](https://adoptium.net/) version 11+
 * [Apache Ant](https://ant.apache.org/) version 1.9.8+

Clone this repo & open a shell in its root, then run:
```bash
cd tlatools/org.lamport.tlatools
ant -f customBuild.xml info compile compile-test dist # Builds tla2tools.jar
java -cp dist/tla2tools.jar tlc2.TLC test-model/pcal/Bakery.tla # Runs an example
ant -f customBuild.xml test # Runs unit tests
```

The unit tests should all succeed.
The compiled `tla2tools.jar` will be output to `tlatools/org.lamport.tlatools/dist/tla2tools.jar`, and can be used the same as any `tla2tools.jar` you download from the releases.

Build & Test Toolbox IDE
------------------------
Install the following dependencies to your path:
 * [Java Development Kit](https://adoptium.net/) version 11+
 * [Apache Ant](https://ant.apache.org/) version 1.9.8+
 * [Apache Maven](https://maven.apache.org/) version 3.9.7+

Clone this repo & open a shell in its root, then run:
```bash
mvn install -Dmaven.test.skip=true # Builds Toolbox
mvn verify # Runs tests
```

The Toolbox distributables will be output in the `toolbox/org.lamport.tla.toolbox.product.product/target/products` directory.

Developing with the Eclipse IDE
-------------------------------
You are free to use your own editor, but this project is largely developed in the [Eclipse](https://www.eclipse.org/) integrated development environment (IDE).

### Developing the TLA⁺ Tools in Eclipse

Developing the TLA⁺ Tools in Eclipse requires the [Eclipse IDE for RCP and RAP Developers](https://www.eclipse.org/downloads/packages/release/2024-06/r/eclipse-ide-rcp-and-rap-developers) edition, or any other edition that comes with the OSGi Plugin Development Extension.
After you have installed Eclipse, use it open the `tlatools/org.lamport.tlatools` project directory.
You should then be able to build, run, test, and debug the TLA⁺ Tools.

Note that running build or test operations with Ant can occasionally interfere with Eclipse's build system and cause Eclipse to report nonexistent compilation errors in the UI.
For this reason you should run Ant from within Eclipse by opening Window > Show View > Other > Ant > Ant, then adding the `customBuild.xml` file and running selected targets.
This will also add the `RunAllTLCTests` target to the external tools runner menu.

If you ran Ant from your CLI for whatever reason and are encountering issues with nonexistent compilation errors in Eclipse, you can resolve them by right-clicking the project in the Workspace pane then selecting "Refresh".
This can also be set to refresh automatically in the Eclipse settings; open them by clicking Eclipse > Settings on macOS or Window > Preferences on Linux, then check the box at General > Workspace > "Refresh using native hooks or polling".
Note, however, that enabling this setting may cause compilation failures when running Ant from your CLI while Eclipse is open; you should only enable it if you are running Ant solely from within Eclipse.
The setting also helps Eclipse pick up changes as you switch between git branches.

### Developing the Toolbox in Eclipse

For instructions on how to set up Eclipse to develop the Toolbox IDE, read [this](general/ide/README.md).

Using Git Effectively
---------------------

Git was designed to shine in a federated open source development model.
You are likely to require use of more of its features than you would in a corporate development environment.
Here is a brief primer on often-used git functionality when developing for this project.
It assumes a basic familiarity with common git operations like clone, commit, push, and pull.
There are countless free and paid git guides available online; [here](https://www.git-scm.com/doc) are the docs from the git project itself, and [here](https://wizardzines.com/git-cheat-sheet.pdf) is a useful cheat-sheet from Julia Evans.

### Dealing with multiple remotes

Your first step when developing for this project will be to fork it so you have your own copy to work with under your own GitHub account.
Then, you will clone that fork to your local development machine.
However, you will also want to occasionally synchronize your fork with the original (which we might call *upstream*).
For this you will need to define multiple *remotes* that you can push to and pull from.
To list all the remotes defined for your local cloned repo, run:
```bash
git remote
```
If you have a remote named `origin`, you can see the repository it is pointing to with:
```bash
git remote get-url origin
```
You want to have at least two remotes, one pointing to upstream and another pointing to your user fork.
Add an `upstream` remote with this command:
```bash
git remote add upstream git@github.com:tlaplus/tlaplus.git
```
If you cloned your repo from your user fork, you can also rename `origin` to `user` or something similarly descriptive as follows:
```bash
git remote rename origin user
```
If you want to get the latest changes from upstream, you can then run:
```bash
git checkout master
git pull upstream master
```
Then, either merge or rebase on those changes to get them into your local development branches.

### Modifying past commits

When you're working with others, you don't want to subject them to your raw git commit history.
Often you accumulate commits that are only periodic check-ins to avoid losing work instead of logically-contained sets of changes.
Git's `rebase` command is much-feared but powerful, and you should become very familiar with it.
If you are developing a feature in a branch, you can enter rebase mode by running:
```bash
git rebase -i master
```
This will take you to a text editor where you can command git to do all kinds of things with your commits!
You can:
 * Reorder them
 * Squash several of them into a single commit
 * Select them to be manually edited/amended

Then, git will run through all your commits sequentially and execute whatever manipulations you indicated.
Squashing is very useful for combining those periodic check-in commits into something meaningful.
Editing is useful for responding to PR review comments; most people know about using `git --amend` to apply changes to the latest commit, but using the `rebase` edit option lets you apply changes to commits in the past!

### Splitting up commits and PRs

While rebasing, you can also use editing to split a single commit up into multiple commits.
This is fairly straightforward when the changes are in different files, but if you want some changes within a single file to go in one commit and some to go in another commit, you can accomplish this interactively with:
```bash
git add --patch <filename>
```
Sometimes you might want to split your commits across multiple branches so they can be in separate PRs.
For this, switch to a new branch then use:
```bash
git cherry-pick <commit hash>
```
This will add the specified commit to the head of your new branch.
You can then rebase your original feature branch to remove that commit.

### Developer Certificate of Origin (DCO) sign-off

Due to legal disputes in the mid-2000s, all commits to projects under the Linux Foundation are required to contain a [Developer Certificate of Origin (DCO)](https://en.wikipedia.org/wiki/Developer_Certificate_of_Origin) sign-off (note this is different from signing commits with a GPG key).
This basically says that you (the developer) were entirely responsible for writing the code in the commit and that you are legally permitted to contribute it under a permissive license (it isn't copied from proprietary code, for example).
In git this is easily done by adding an extra `-s` flag as you commit:
```bash
git commit -s -am "Commit message here"
```
Don't worry too much about forgetting this; the CI will catch it and GitHub provides a page with simple instructions to retroactively add DCO sign-off to past commits.
Eventually adding the `-s` flag will become muscle memory.

Release Channels
----------------

Nightly builds of the [Toolbox](https://nightly.tlapl.us/products/) and [tla2tools](https://nightly.tlapl.us/dist/) are found at https://nightly.tlapl.us/products/ and https://nightly.tlapl.us/dist/.
The Toolbox contains the latest version of tla2tools.jar for command-line usage in its root directory.

It is also possible to configure the Toolbox to [automatically update to nightly (experimental) builds](https://nightly.tlapl.us/doc/update/update-preferences.html).  

Note that it is called nightly for historical reasons, but builds are actually triggered by commits.

### Linux

For dpkg-based Linux derivates such as Debian and Ubuntu, you can add the Toolbox's nightly package repository to your source list:

```
$ cat /etc/apt/sources.list.d/tlaplus.list
deb https://nightly.tlapl.us/toolboxUpdate/ ./
$ curl -fsSL https://tla.msr-inria.inria.fr/jenkins.pub | sudo apt-key add -
```

### macOS

The Homebrew community makes the Toolbox's nightly builds available as a [cask](https://github.com/Homebrew/homebrew-cask-versions/blob/master/Casks/tla-plus-toolbox-nightly.rb) through [homebrew versions](https://github.com/Homebrew/homebrew-cask-versions#usage):

```bash
$ brew tap homebrew/cask-versions
$ brew install tla-plus-toolbox-nightly
```

Code Formatting and Style
-------------------------

TLA⁺ has no strict formatting requirements; focus on substance over style.
The source code contains a wide variety of styles, and although that can sometimes be distracting, standardizing on one is not a priority for the project.

That said, it is worth following a few guiding principles:

 1. Modifications should copy the style of nearby code rather than change it.  This helps keep modifications focused so they are easy to review and [bisect](https://git-scm.com/docs/git-bisect).
 2. New source files should have a consistent style.

For new Java code we recommend (but do not require):

 - Each `public` class and method should have a javadoc description of its purpose and behavior.
 - Use 4 spaces for indentation.  If you choose to use tabs instead, do not mix tabs and spaces.
 - Put opening curly braces (`{`) on the same line as the corresponding declaration or statement.
 - Include braces for single-statement bodies of statements like `if` and `while`, even though they are optional.
 - Avoid lines longer than 120 characters.

Note that all of the project's Java source files are encoded in UTF-8 and may therefore contain mathematical characters.
