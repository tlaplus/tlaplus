// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 16:11:13 PST by lamport
//      modified on Fri Jun  1 15:26:01 PDT 2001 by yuanyu

package tlc2;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Simulator;
import tlc2.util.RandomGenerator;
import util.ToolIO;

public class Generator {
  /*
   * This TLA trace generator generates random execution traces:
   *     srcjava tlc.Generator spec[.tla]
   *
   * The command line provides the following options:
   *  o -deadlock:    do not check for deadlock.
   *                  Defaults to checking deadlock if not specified   
   *  o -f file:      the file storing the traces. Defaults to spec_trace
   *  o -d num:       the max length of the trace. Defaults to 10
   *  o -config file: the config file.  Defaults to spec.cfg
   *  o -coverage seconds: collect coverage information on the spec,
   *                       print out the information every seconds
   *    Defaults to no coverage if not specified
   *  o -n num:       the max number of traces. Defaults to 10
   *  o -s:           the seed for random simulation
   *                  Defaults to a random seed if not specified
   *  o -aril num:    Adjust the seed for random simulation
   *                  Defaults to 0 if not specified
   */
  public static void main(String[] args) {
    System.out.println("TLC trace generator, " + TLCGlobals.versionOfTLC);

    String mainFile = null;
    String traceFile = null;
    boolean deadlock = true;
    String configFile = null;
    int traceDepth = 10;
    int traceNum = 10;
    boolean noSeed = true;
    long seed = 0;
    long aril = 0;

    int index = 0;
    while (index < args.length) {
      if (args[index].equals("-f")) {
	index++;
	if (index >= args.length) {
	  printErrorMsg("Error: no argument given for -f option.");
	  return;
	}
	traceFile = args[index++];
      }
      else if (args[index].equals("-deadlock")) {
	index++;
	deadlock = false;
      }
      else if (args[index].equals("-d")) {
	index++;
	if (index >= args.length) {
	  printErrorMsg("Error: no argument given for -d option.");
	  return;
	}
	traceDepth = Integer.parseInt(args[index]);
	index++;
      }
      else if (args[index].equals("-n")) {
	index++;
	if (index >= args.length) {
	  printErrorMsg("Error: no argument given for -n option.");
	  return;
	}
	traceNum = Integer.parseInt(args[index]);
	index++;
      }
      else if (args[index].equals("-coverage")) {
 	index++;
 	if (index < args.length) {
 	  try {
 	    TLCGlobals.coverageInterval = Integer.parseInt(args[index]) * 60 * 1000;
	    if (TLCGlobals.coverageInterval < 0) {
	      printErrorMsg("Error: expect a nonnegative integer for -coverage option.");
	      return;
	    }
 	    index++;
 	  }
 	  catch (Exception e) {
 	    printErrorMsg("Error: An integer for coverage report interval required." +
 			  " But encountered " + args[index]);
 	    return;
 	  }
 	}
 	else {
 	  printErrorMsg("Error: coverage report interval required.");
	  return;
 	}
      }
      else if (args[index].equals("-s")) {
	index++;
	if (index < args.length) {
	  seed = Long.parseLong(args[index++]);
	  noSeed = false;
	}
	else {
	  printErrorMsg("Error: seed required.");
	  return;
	}
      }
      else if (args[index].equals("-aril")) {
	index++;
	if (index < args.length) {
	  aril = Long.parseLong(args[index++]);
	}
	else {
	  printErrorMsg("Error: aril required.");
	  return;
	}
      }
      else if (args[index].equals("-config")) {
	index++;
	if (index < args.length) {
	  configFile = args[index];
	  int len = configFile.length();
	  if (configFile.startsWith(".cfg", len-4)) {
	    configFile = configFile.substring(0, len-4);
	  }
	  index++;
	}
	else {
	  printErrorMsg("Error: config file required.");
	  return;
	}
      }
      else {
	if (args[index].charAt(0) == '-') {
	  printErrorMsg("Error: unrecognized option: " + args[index]);
	  return;
	}
	if (mainFile != null) {
	  printErrorMsg("Error: more than one input files: " + mainFile
			+ " and " + args[index]);
	  return;
	}
	mainFile = args[index++];
	int len = mainFile.length();
	if (mainFile.startsWith(".tla", len-4)) {
	  mainFile = mainFile.substring(0, len-4);
	}
      }
    }
    if (mainFile == null) {
      printErrorMsg("Error: Missing input TLA+ module.");
      return;
    }
    if (traceFile == null) traceFile = mainFile + "_trace";
    if (configFile == null) configFile = mainFile;
    
    // Start generating traces:
    try {
      RandomGenerator rng = new RandomGenerator();
      if (noSeed) {
	seed = rng.nextLong();
	rng.setSeed(seed);
      }
      else {
	rng.setSeed(seed, aril);
      }
      ToolIO.out.println("Generating random traces with seed " + seed + ".");
      Simulator simulator = new Simulator(mainFile, configFile, traceFile,
					  deadlock, traceDepth, traceNum,
					  rng, seed, true, null, /* no spec obj */ null);
      simulator.simulate();
    }
    catch (Exception e) {
      // Assert.printStack(e);
        MP.printError(EC.GENERAL, "generating traces", e);  // LL changed call 7 April 2012
    }
    //System.exit(0); //SZ: no-op removed
  }

  // TODO replace 
  private static void printErrorMsg(String msg) {
      MP.printError(EC.WRONG_COMMANDLINE_PARAMS_SIMULATOR, msg);
  }

}
