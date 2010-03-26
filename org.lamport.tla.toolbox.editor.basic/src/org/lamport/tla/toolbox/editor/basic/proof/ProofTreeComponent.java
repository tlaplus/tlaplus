package org.lamport.tla.toolbox.editor.basic.proof;

import org.eclipse.jface.text.Position;

/**
 * Represents a part of the proof tree. This can be a provable part
 * such as a theorem, lemma, or proof step, or it can be a proof.
 * 
 * @author Daniel Ricketts
 *
 */
public abstract class ProofTreeComponent
{

    /**
     * The position of this component of the
     * proof tree.
     */
    protected Position position;
    /**
     * The root of the proof tree
     * containing this component. This is the theorem,
     * lemma, corollary, etc. of the tree.
     */
    protected Provable root;
    /**
     * The parent component of this
     * proof tree component.
     */
    protected ProofTreeComponent parent;

    /**
     * Returns the position of this component of the
     * proof tree.
     * 
     * @return
     */
    public Position getPosition()
    {
        return position;
    }

    /**
     * Returns the parent component of this
     * proof tree component.
     * 
     * @return
     */
    public ProofTreeComponent getParent()
    {
        return parent;
    }

    /**
     * Instantiated by the parent and initial offset and length as returned by
     * the parser.
     * 
     * The offset and length can change as the user edits, so these are
     * only the initial values.
     * 
     * @param offset initial offset of this component
     * @param length initial length of this component
     * @param parent parent of this component
     */
    public ProofTreeComponent(int offset, int length, ProofTreeComponent parent)
    {
        position = new Position(offset, length);
        // annotation = new ProjectionAnnotation();
        this.parent = parent;
        if (parent != null)
        {
            // parent is null if this component is the root
            this.root = parent.root;
            this.root.addComponent(this);
        } else
        {
            this.root = (Provable) this;
        }

    }

    /**
     * Returns the root of the proof tree
     * containing this component. This is the theorem,
     * lemma, corollary, etc. of the tree.
     * 
     * @return
     */
    public Provable getRoot()
    {
        return root;
    }

}
