package org.lamport.tla.toolbox.tool.tlc.model;

import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;

import junit.framework.TestCase;

/**
 * Test of the typed set factory
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TypedSetTest extends TestCase
{

    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.model.TypedSet#parseSet(java.lang.String)}.
     */
    public void testParseSet1()
    {
        
        TypedSet reference = new TypedSet();
        reference.setValues(new String[]{"a", "b", "c", "d", "dsfdf"});
        assertEquals(reference, TypedSet.parseSet("a, b, c,     d,   dsfdf"));
    }

    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.model.TypedSet#parseSet(java.lang.String)}.
     */
    public void testParseSet2()
    {
        TypedSet reference = new TypedSet();
        reference.setValues(new String[]{"1", "2", "p", "h!@#$%^&*()_", "dsfdf"});
        assertEquals(reference, TypedSet.parseSet("1, 2, p, h!@#$%^&*()_, dsfdf"));
    }

    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.model.TypedSet#parseSet(java.lang.String)}.
     */
    public void testParseSet3()
    {
        // positive test
        TypedSet reference = new TypedSet();
        reference.setValues(new String[]{"1", "2", "3", "4", "5"});
        reference.setType("p");
        TypedSet sample = TypedSet.parseSet("p_1,     p_2,    p_3, \n p_4, p_5");
        assertEquals(reference, sample);
    }

    
    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.model.TypedSet#parseSet(java.lang.String)}.
     */
    public void testParseSet4()
    {
        TypedSet reference = new TypedSet();
        reference.setValues(new String[]{"p_1", "i_2", "p_3", "p_4", "p_5"});
        TypedSet sample = TypedSet.parseSet("p_1, i_2, p_3, p_4, p_5");
        assertEquals(reference, sample);
    }

    
    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.model.TypedSet#parseSet(java.lang.String)}.
     */
    public void testParseSet5()
    {
        TypedSet reference = new TypedSet();
        reference.setValues(new String[]{"p_", "p_2", "p_3", "p_4", "p_5"});
        TypedSet sample = TypedSet.parseSet("p_, p_2, p_3, p_4, p_5");
        assertEquals(reference, sample);
    }

    /**
     * Test method for {@link org.lamport.tla.toolbox.tool.tlc.model.TypedSet#parseSet(java.lang.String)}.
     */
    public void testParseSet6()
    {
        // null set
        TypedSet reference = new TypedSet();
        TypedSet sample = TypedSet.parseSet("");
        assertEquals(reference, sample);
        
        sample = TypedSet.parseSet(null);
        assertEquals(reference, sample);

        sample = TypedSet.parseSet(", , , , ");
        assertEquals(reference, sample);

        sample = TypedSet.parseSet("{, , , ,}");
        assertEquals(reference, sample);

    }

}
