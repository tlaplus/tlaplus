You can help make the TLA+ tools better by allowing TLC to collect execution statistics. Execution statistics are made [publicly available](https://exec-stats.tlapl.us) on the web and contain the following information:

* Total number of cores and cores assigned to TLC
* Heap and off-heap memory allocated to TLC
* TLC version  (git commit SHA)
* If breadth-first search, depth-first search or simulation mode is active
* TLC implemenation for the sets of seen and unseen states
* If TLC has been launched from an IDE
* Name, version, and architecture of the OS
* Vendor, version, and architecture of JVM
* The current date and time
* An installation ID which allows to group execution statistic (optionally)

Execution statistics do not contain personal information. You can opt-out any time.
