Contributing to TLA⁺
--------------------

TL;DR: engage maintainers early & often, be surgical in your changes, and write lots of tests.

We welcome contributions to this open source project!
Before beginning work, please take some time to familiarize yourself with our development processes and expectations.
The TLA⁺ tools are used to validate safety-critical systems, so maintaining quality is paramount.
The existing code can also be quite complicated to modify and it is difficult to review changes effectively.
So, there are several practices that are necessary for having a good contribution experience.
The last thing anybody wants is for you to feel as though you have wasted your time!
If you open a massive pull request (PR) out of nowhere it is **very unlikely to be merged**.
Follow this guide to ensure your effort is put to the best possible use.

Always remember that we are all volunteers here.
Be kind to everybody!
You can review our Code of Conduct [here](.github/CODE_OF_CONDUCT.md).

The Contribution Process & Style
--------------------------------

The most important step is to engage with existing developers & maintainers before beginning work.
The best way to do this is to comment on an issue you want to fix, or open a new issue if a suitable candidate does not exist.
It is also very helpful to join the [monthly online community meeting](https://groups.google.com/g/tlaplus/c/CpAEnrf-DHQ/m/YrORpIfSBwAJ) to introduce yourself and speak with people directly.
The development team will help you better understand the scope & difficulty of the proposed changes, along with what parts of the codebase they'll touch and what additional tests are required to safely merge them.
Building & maintaining consensus around these aspects will ensure a smooth review & merge process.

To begin work on your change, fork this repository then create an appropriately-named branch to track your work.
You will eventually submit a PR between your feature branch and the master branch of this repository, at which point developers & maintainers will review your changes.
After integrating this feedback your PR will then hopefully be merged.

When creating and submitting your changes, closely follow these guidelines:
 * **Be surgical:** What is the smallest diff you can make that still accomplishes your goal?
 Avoid the urge to fix unrelated stylistic issues in a file you are changing.
 * **Write tests first:** If you're changing a specific part of the codebase, first ensure it has good test coverage; if it does, write a few more tests yourself anyway!
 Writing tests is a great way to learn how the code functions.
 If possible, submit your tests in a separate PR so their benefits can be realized immediately.
 We don't fully subscribe to Test-Driven Development (TDD) but having good existing test coverage of a changed area is a prerequisite to changes being merged.
 * **Split up your changes:** If parts of your changes provide some benefit by themselves - like additional tests - split them into a separate PR.
 It is preferable to have several small PRs merged quickly than one large PR that takes longer to review.
 * **Craft your commits well:** This can require advanced git knowledge (see [DEVELOPING.md](DEVELOPING.md)).
 Treat your commits as forms of communication, not a way to bludgeon the codebase into shape.
 You don't need to check this, but ideally the build & tests should pass on every commit.
 This means you will often be amending commits as you work instead of adding new ones.

When you open a PR against this repo, the continuous integration (CI) checks will run.
These ensure your changes do not break the build & tests.
While you can run most of these checks locally, if you'd like to run the CI at any time you can open a PR between your feature branch and the master branch of *your own* fork of this repo.

Contribution Possibilities
--------------------------

These tools have a large number existing issues to fix, which you can see on the repo's [issues tab](https://github.com/tlaplus/tlaplus/issues).
In particular, consider looking at issues [tagged with "help wanted"](https://github.com/tlaplus/tlaplus/issues?q=is%3Aopen+is%3Aissue+label%3A%22help+wanted%22).
For new developers, there are issues [tagged "good first issue"](https://github.com/tlaplus/tlaplus/labels/good%20first%20issue).

For new features, there are a number of [substantial improvements we'd like to see implemented](general/docs/contributions.md).
If you have an idea for a new feature, open an issue in this repository to start a discussion.
For more fundamental proposals that involve changes to the TLA⁺ language itself, you can [open a RFC](https://github.com/tlaplus/rfcs/issues).
Often it will be necessary to build community support for your idea; for this you can use the [mailing list](https://groups.google.com/g/tlaplus) and especially the [monthly online community meeting](https://groups.google.com/g/tlaplus/c/CpAEnrf-DHQ/m/YrORpIfSBwAJ).
Expressions of goodwill like volunteering labor to review pending PRs is also appreciated!

Non-code contributions are also welcome!
There is ample work available in expanding developer documentation (like this very document) or user-facing TLA⁺ documentation.
We also collect [quality metrics](https://sonarcloud.io/organizations/tlaplus/projects), and the reports indicate several low-hanging fruits to pick.

Getting Started
---------------

Take the time to set up your local development environment.
See [DEVELOPING.md](DEVELOPING.md) for details.
Good luck, and have fun!

