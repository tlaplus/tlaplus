package org.lamport.tla.toolbox.spec.parser;

import org.lamport.tla.toolbox.spec.Spec;

/**
 * Basic parser launcher interface
 * @author zambrovski
 */
public interface IParserLauncher
{
    /**
     * Launches the spec parsing
     * @param spec specification handle
     * @return the parse status (which should also be saved in the spec)
     */
    public int parseSpecification(Spec spec);
}
