package org.lamport.tla.toolbox.editor.basic.proof;

import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;

/**
 * Container class for the {@link Position} and {@link ProjectionAnnotation}
 * for a fold.
 * 
 * @author drickett
 * @deprecated
 *
 */
public class FoldTuple
{

    private ProjectionAnnotation annotation;
    private Position position;

    public FoldTuple(ProjectionAnnotation annotation, Position position)
    {
        this.position = position;
        this.annotation = annotation;
    }

    public ProjectionAnnotation getAnnotation()
    {
        return annotation;
    }

    public Position getPosition()
    {
        return position;
    }

}
