Is this your first contribution to Open Source? If yes, please read the excellent first time contributor guide at [https://opensource.guide/how-to-contribute/](https://opensource.guide/how-to-contribute/).

Generally, we welcome contributions from volunteers. A number of [improvements we'd like to see implemented](https://github.com/tlaplus/tlaplus/blob/master/general/docs/contributions.md) are listed at [general/docs/contributions.md](https://github.com/tlaplus/tlaplus/blob/master/general/docs/contributions.md) in addition to the [issues tagged with "helpwanted"](https://github.com/tlaplus/tlaplus/issues?q=is%3Aopen+is%3Aissue+label%3A%22help+wanted%22). But we're happy to consider anything you'd like to contribute. However, some parts of the tlaplus repository follow a very strict contribution policy. So before you start working on anything, please [discuss with us](https://github.com/tlaplus/tlaplus/issues) what you want to do. You can do that on the [issues page](https://github.com/tlaplus/tlaplus/issues). We do not want to reject your 1k LOC patch because the actual change is not considered sensible by us.

 

Except for [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html), the TLA<sup>+</sup> tools are maintained in Eclipse. [For instructions on how to setup the Eclipse IDE, please go to general/ide/README.md.](https://github.com/tlaplus/tlaplus/tree/master/general/ide).

Nightly Builds
--------------

Nightly builds of the [Toolbox](https://nightly.tlapl.us/products/) and [tla2tools](https://nightly.tlapl.us/dist/) are found at https://nightly.tlapl.us/products/ and https://nightly.tlapl.us/dist/, the [up-to-date changelog](https://nightly.tlapl.us/changelog.html) is at https://nightly.tlapl.us/changelog.html.  The Toolbox contains the latest version of tla2tools.jar for command-line usage in its root directory.

It is also possible to configure the Toolbox to [automatically update to nightly (experimental) builds](https://nightly.tlapl.us/doc/update/update-preferences.html).  

Note that it is called nightly for historical reasons, but builds are actually triggered by commits.

#### Linux

For dpkg-based Linux derivates such as Debian and Ubuntu, you can add the Toolbox's nightly package repository to your source list:

```
$ cat /etc/apt/sources.list.d/tlaplus.list
deb https://nightly.tlapl.us/toolboxUpdate/ ./
$ curl -fsSL https://tla.msr-inria.inria.fr/jenkins.pub | sudo apt-key add -
```

#### macOS

The Toolbox's nightly builds are also made available as a [cask](https://github.com/Homebrew/homebrew-cask-versions/blob/master/Casks/tla-plus-toolbox-nightly.rb) through [homebrew versions](https://github.com/Homebrew/homebrew-cask-versions#usage):

```bash
$ brew tap homebrew/cask-versions
$ brew install tlaplus-toolbox-nightly
```

Quality Metrics
---------------

We collect [quality metrics](https://sonarcloud.io/organizations/tlaplus/projects). If you want to help out with the project, the reports indicate several low hanging fruits to pick.
