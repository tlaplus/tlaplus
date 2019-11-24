As of December 2019, the tlatools ship with the TraceExplorer command line application.

The current usage of this is as follows; this usage text can also be seen by invoking the application (tla2.TraceExplorer) with no arguments:

	To generate a SpecTE file pair:
			java tlc2.TraceExplorer -generateSpecTE \
				[-source=_directory_containing_prior_run_output_] \
				[-spec=SomethingOtherThanMC] \
				[-overwrite]
		o source defaults to CWD if not specified.
		o spec defaults to 'MC' if not specified.
		o if a SpecTE.tla already exists and overwrite is not specified, execution will halt.

	To pretty print the error states of a previous run:
			java tlc2.TraceExplorer -prettyPrint \
				[-source=_directory_containing_prior_run_output_] \
				[-spec=SomethingOtherThanMC]
		o source defaults to CWD if not specified.
		o spec defaults to 'MC' if not specified.


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
