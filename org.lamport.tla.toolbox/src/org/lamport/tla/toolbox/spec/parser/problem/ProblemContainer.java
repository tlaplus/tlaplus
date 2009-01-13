package org.lamport.tla.toolbox.spec.parser.problem;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IAdapterManager;
import org.eclipse.core.runtime.Platform;

/**
 * Problem storage
 * 
 * @author zambrovski
 */
public class ProblemContainer implements IAdaptable
{
    List storage = null;

    /**
     * Constructs the problem holder
     */
    public ProblemContainer()
    {
        reset();
    }

    /**
     * Adds a problem to the container
     * 
     * @param problemHolder
     *            a problem object
     */
    public void addProblem(Problem problemHolder)
    {
        if (problemHolder == null)
        {
            return;
        }
        storage.add(problemHolder);
    }

    /**
     * Deletes all errors from the problem container
     */
    public void reset()
    {
        storage = new LinkedList();
    }

    /**
     * Retrieves a list of all problems of given severity
     * 
     * @param severity
     *            a value specifying which severity levels should be included (use conjunction like
     *            {@link Problem#ABORT} | {@link Problem#WARNING} | {@link Problem#ERROR})
     * @return a list of problems ordered by type: first {@link Problem#WARNING}, then {@link Problem#ERROR}, finally
     *         {@link Problem#ABORT}
     */
    public List getProblems(int severity)
    {
        List problems = new LinkedList();

        if (severity / Problem.WARNING == 1)
        {
            for (int i = 0; i < storage.size(); i++)
            {
                if (((Problem) storage.get(i)).type == Problem.WARNING)
                {
                    problems.add(storage.get(i));
                }
            }
            severity = severity % Problem.WARNING;
        }
        if (severity / Problem.ERROR == 1)
        {
            for (int i = 0; i < storage.size(); i++)
            {
                if (((Problem) storage.get(i)).type == Problem.ERROR)
                {
                    problems.add(storage.get(i));
                }
            }
            severity = severity % Problem.ERROR;
        }
        if (severity / Problem.ABORT == 1)
        {
            for (int i = 0; i < storage.size(); i++)
            {
                if (((Problem) storage.get(i)).type == Problem.ABORT)
                {
                    problems.add(storage.get(i));
                }
            }
            // severity = severity % Problem.ABORT;
        }

        return problems;
    }

    /**
     * Retrieves number of problems of given type(s)
     * 
     * @param severity
     *            a value specifying which severity levels should be included (see
     *            {@link ProblemContainer#getProblems(int)})
     * @return number of problem of given type(s)
     */
    public int getNumberOfProblems(int severity)
    {
        return getProblems(severity).size();
    }

    /**
     * Reports if problems of any level exist
     * 
     * @return true iff no problems stored, false otherwise
     */
    public boolean isEmpty()
    {
        return storage.isEmpty();
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.core.runtime.IAdaptable#getAdapter(java.lang.Class)
     */
    public Object getAdapter(Class adapter)
    {
        // lookup the IAdapterManager service
        IAdapterManager manager = Platform.getAdapterManager();
        // forward the request to IAdapterManager service
        return manager.getAdapter(this, adapter);

    }
}
