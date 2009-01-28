package org.lamport.tla.toolbox.spec.parser;

import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.spec.Spec;

/**
 * Basic parser launcher interface
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IParserLauncher
{
    /**
     * Launches the spec parsing
     * @param spec specification handle
     * @param monitor the monitor to report progress
     * @return the parse status (which should also be saved in the spec)
     */
    public int parseSpecification(Spec spec, IProgressMonitor monitor);
}
