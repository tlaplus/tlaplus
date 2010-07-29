package org.lamport.tla.toolbox.tool.prover.job;

/**
 * This interface contains constants for
 * all options that can be used to launch the prover.
 * 
 * The description of each option is copied from the tlapm-toolbox
 * interface spec.
 * 
 * @author Daniel Ricketts
 *
 */
public interface ITLAPMOptions
{

    /**
     * --meth
     * 
     * Changes the default method for proving 
     * (the default is zenon with 10 second time-out and isabelle auto fallback)
     */
    public static final String METH = "--meth";
    /**
     * --solver
     * 
     * Which smt solver to use.
     */
    public static final String SOLVER = "--solver";
    /**
     * --paranoid
     * 
     * Asks isabelle to check trivial obligations
     */
    public static final String PARANOID = "--paranoid";
    /**
     * --isaprove
     * 
     * Sends obligations to isabelle to be proved as soon as zenon fails 
     * or when isabelle is called by a pragma.
     */
    public static final String ISAPROVE = "--isaprove";
    /**
     * --noproving
     * 
     * Does not send any obligations to backends. Checks if an obligation is 
     * trivial or not and considers previous results in the fingerprint files. 
     * If an obligation is not trivial and does not appear in the fingerprints 
     * file, then the only message sent to the toolbox has a status "to be proved".
     */
    public static final String NOPROVING = "--noproving";
    /**
     * --threads <num>
     * 
     * Num is an integer giving the number of worker backend threads used. 
     * Default is the number of cores.
     */
    public static final String THREADS = "--threads";
    /**
     * -C
     * 
     * Sends all obligations to isabelle for checking except trivial obligations 
     * (if --paranoid is not called), already checked obligations, and obligations 
     * on which isabelle has already failed or succeeded.
     */
    public static final String CHECK = "-C";
    /**
     * --wait <t>
     * 
     * t is an integer. After sending an obligation to a backend, the pm waits 
     * t seconds. If the backend has not finished on that obligation after those 
     * t seconds, the pm sends an obligation message with status "being proved" 
     * to the toolbox for that obligation. The default value is 3.
     */
    public static final String WAIT = "--wait";
    /**
     * --cleanfp
     * 
     * Erase the fingerprint file before processing the module. Adds new fingerprints.
     */
    public static final String CLEANFP = "--cleanfp";
    /**
     * --nofp
     * 
     * Erase fingerprints of obligations considered by the present launch of 
     * the toolbox (i.e. located between bl and el). Adds new fingerprints.
     */
    public static final String NOFP = "--nofp";
    /**
     * --nofpl b e
     * 
     * Erase fingerprints of obligations both (considered by the present launch of 
     * the toolbox) and (located between lines b and e). Adds new fingerprints.
     */
    public static final String NOFPL = "--nofpl";
    /**
     * --fpdir <dir>
     * 
     * Sets to dir the directory from which the fingerprints file is loaded and to 
     * which it is saved. (accepts both complete and relative pathnames)
     */
    public static final String FPDIR = "--fpdir";
    /**
     * --safefp
     * 
     * Checks isabelle and zenon versions before loading fingerprints. Only uses 
     * fingerprints whose zenon and isabelle versions equal the zenon and isabelle 
     * versions currently used by tlapm.
     */
    public static final String SAFEFP = "--safefp";
    /**
     * --help
     * 
     * Show the help message and exit.
     */
    public static final String HELP = "--help";
    /**
     * --version
     * 
     * Show version number and exit.
     */
    public static final String VERSION = "--version";
    /**
     * --verbose
     * 
     * Produce verbose messages.
     */
    public static final String VERBOSE = "--verbose";
    /**
     * --where
     * 
     * Show location of standard library and exit.
     */
    public static final String WHERE = "--where";
    /**
     * --config
     * 
     * Show configuration and exit.
     */
    public static final String CONFIG = "--config";
    /**
     * --summary
     * 
     * Show summary of theorems (implies -N and not -C).
     */
    public static final String SUMMARY = "--summary";
    /**
     * --timing
     * 
     * Show runtime statistics.
     */
    public static final String TIMING = "--timing";
    /**
     * -I <dir>
     * 
     * Add <dir> to search path.
     */
    public static final String ADD_DIR = "-I";
    /**
     * -d <dir>
     * 
     * Send generated output to <dir>.
     */
    public static final String SEND_DIR = "-d";
    /**
     * -k
     * 
     * Keep going on backend failures.
     */
    public static final String KEEP_GOING = "-k";
    /**
     * -N
     * 
     * Do not run any backend verifiers.
     * (-> similar to --noproving)
     */
    public static final String NO_BACKEND = "-N";
    /**
     * --trust {[-]<backend>}
     * 
     * Enable/disable trust on backends (see --trust list).
     */
    public static final String TRUST = "--trust";
    /**
     * --noflatten
     * 
     * Do not flatten obligations.
     */
    public static final String NO_FLATTEN = "--noflatten";
    /**
     * --nonormal
     * 
     * Do not normalize obligations before printing.
     */
    public static final String NO_NORMAL = "--nonormal";
    /**
     * --debug {[-]<flag>}
     * 
     * Enable/disable debugging flags.
     */
    public static final String DEBUG = "--debug";

}
