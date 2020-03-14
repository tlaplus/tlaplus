As of December 2019, the tlatools ship with the TraceExplorer command line application.

The current usage of this is as follows; this usage text can also be seen by invoking the application (tla2.TraceExplorer) with no arguments:

	To generate a SpecTE file pair:
			java tlc2.TraceExplorer -generateSpecTE \
				[-source=_directory_containing_prior_run_output_] \
				[-overwrite] \
				SpecName
		o source defaults to CWD if not specified.
		o if a SpecTE.tla already exists and overwrite is not specified, execution will halt.
		o if no SpecName is specified, output will be expected to arrive via stdin; -source will be ignored in this case.

	To pretty print the error states of a previous run:
			java tlc2.TraceExplorer -prettyPrint \
				[-source=_directory_containing_prior_run_output_] \
				SpecName
		o source defaults to CWD if not specified.
		o if no SpecName is specified, output will be expected to arrive via stdin; -source will be ignored in this case.


------------------------------------------------------------------------------------

An example of the pretty print output is:

algebraic:Model_1_SnapShot_1576778796288 loki$ java ... tlc2.TraceExplorer -prettyPrint -source=/Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/Queens/Queens.toolbox/FourQueens/
 <Initial predicate>
	/\  todo = {<<>>}
	/\  sols = {}

 <PlaceQueen line 50, col 15 to line 62, col 26 of module Queens>
	/\  todo = {<<1>>, <<2>>, <<3>>}
	/\  sols = {}

 <PlaceQueen line 50, col 15 to line 62, col 26 of module Queens>
	/\  todo = {<<2>>, <<3>>, <<1, 3>>}
	/\  sols = {}

 <PlaceQueen line 50, col 15 to line 62, col 26 of module Queens>
	/\  todo = {<<3>>, <<1, 3>>}
	/\  sols = {}

 <PlaceQueen line 50, col 15 to line 62, col 26 of module Queens>
	/\  todo = {<<1, 3>>, <<3, 1>>}
	/\  sols = {}

 <PlaceQueen line 50, col 15 to line 62, col 26 of module Queens>
	/\  todo = {<<3, 1>>}
	/\  sols = {}

 <PlaceQueen line 50, col 15 to line 62, col 26 of module Queens>
	/\  todo = {}
	/\  sols = {}

algebraic:Model_1_SnapShot_1576778796288 loki$ 

------------------------------------------------------------------------------------

An example of a piped run from TLC:

algebraic:FourQueens loki$ /Library/Java/JavaVirtualMachines/adoptopenjdk-13.jdk/Contents/Home/bin/java -XX:MaxDirectMemorySize=5460m -Xmx2732m -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -XX:+UseParallelGC -Dfile.encoding=UTF-8 -classpath /Users/loki/arbeit/microsoft/dev/tlaplus/git/tlaplus/tlatools:/Users/loki/arbeit/microsoft/dev/tlaplus/git/tlaplus/tlatools/lib/*:/Users/loki/arbeit/microsoft/dev/tlaplus/git/tlaplus/tlatools/lib/javax.mail/*:/Users/loki/arbeit/microsoft/dev/tlaplus/git/tlaplus/tlatools/class tlc2.TLC -fpbits 1 -fp 4 -config MC.cfg -coverage 3 -workers 1 -tool -metadir /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/Queens/Queens.toolbox/FourQueens MC | /Library/Java/JavaVirtualMachines/adoptopenjdk-13.jdk/Contents/Home/bin/java -XX:+UseParallelGC -Dfile.encoding=UTF-8 -classpath /Users/loki/arbeit/microsoft/dev/tlaplus/git/tlaplus/tlatools:/Users/loki/arbeit/microsoft/dev/tlaplus/git/tlaplus/tlatools/lib/*:/Users/loki/arbeit/microsoft/dev/tlaplus/git/tlaplus/tlatools/lib/javax.mail/*:/Users/loki/arbeit/microsoft/dev/tlaplus/git/tlaplus/tlatools/class tlc2.TraceExplorer -generateSpecTE
Parsing file /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/Queens/Queens.toolbox/FourQueens/MC.tla
Parsing file /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/Queens/Queens.toolbox/FourQueens/Queens.tla
Parsing file /Users/loki/arbeit/microsoft/dev/quaeler_repo/tlaplus/tlatools/class/tla2sany/StandardModules/TLC.tla
Parsing file /Users/loki/arbeit/microsoft/dev/quaeler_repo/tlaplus/tlatools/class/tla2sany/StandardModules/Naturals.tla
Parsing file /Users/loki/arbeit/microsoft/dev/quaeler_repo/tlaplus/tlatools/class/tla2sany/StandardModules/Sequences.tla
Parsing file /Users/loki/arbeit/microsoft/dev/quaeler_repo/tlaplus/tlatools/class/tla2sany/StandardModules/FiniteSets.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module Queens
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module MC
Starting... (2019-12-22 12:56:00)
The file /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/Queens/Queens.toolbox/FourQueens/SpecTE.tla has been created.
The file /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/Queens/Queens.toolbox/FourQueens/SpecTE.cfg has been created.
algebraic:FourQueens loki$ 

