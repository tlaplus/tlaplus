package org.lamport.tla.toolbox.spec.parser.test;

import java.util.Arrays;
import java.util.List;

import org.lamport.tla.toolbox.spec.parser.ParserDependencyStorage;

import junit.framework.TestCase;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParserDependencyStorageTest extends TestCase
{

    ParserDependencyStorage store = null;

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    protected void setUp() throws Exception
    {
        super.setUp();
        store = new ParserDependencyStorage();
    }

    /**
     * module1 -> extend1, extend2
     * extend2 -> extend1
     */
    public void testStore1()
    {
        store.put("module1", Arrays.asList(new String[]{"extend1", "extend2", "extend1"}));
        
        assertTrue(store.getListOfModules("extend1").contains("module1") && store.getListOfModules("extend1").size() == 1);
        assertTrue(store.getListOfModules("extend2").contains("module1") && store.getListOfModules("extend2").size() == 1);
    }
    
    /**
     * A -> E, D 
     * D -> E
     * B -> C, D
     * C -> E
     */
    public void testStore2()
    {
        store.put("A", Arrays.asList(new String[]{"E", "D", "E"}));
        store.put("B", Arrays.asList(new String[]{"C", "E", "D", "E"}));
        
        List cModules = store.getListOfModules("C");
        List dModules = store.getListOfModules("D");
        List eModules = store.getListOfModules("E");
        
        assertEquals(1, cModules.size());
        assertTrue(cModules.contains("B"));

        assertEquals(2, dModules.size());
        assertTrue(dModules.contains("A") && dModules.contains("B"));

        assertEquals(2, eModules.size());
        assertTrue(eModules.contains("B") && eModules.contains("A"));
    }

    
    /**
     * A -> E, D 
     * D -> E
     * B -> C, D
     * C -> E
     * then a parse fail of A
     * only the following should remain
     * B -> C, D
     * D -> E
     * C -> E
     */
    public void testStore2withFail()
    {
        store.put("A", Arrays.asList(new String[]{"E", "D", "E"}));
        store.put("B", Arrays.asList(new String[]{"C", "E", "D", "E"}));
        store.parseFailed("A");
        
        List cModules = store.getListOfModules("C");
        List dModules = store.getListOfModules("D");
        List eModules = store.getListOfModules("E");
        
        assertEquals(1, cModules.size());
        assertTrue(cModules.contains("B"));

        assertEquals(1, dModules.size());
        assertTrue(dModules.contains("B"));

        assertEquals(1, eModules.size());
        assertTrue(eModules.contains("B"));
    }
    
    /**
     * A -> B, C 
     * A -> C, D
     * only the following should remain
     * A -> C, D
     */
    public void testStoreTwice()
    {
        List modules1 = store.put("A", Arrays.asList(new String[]{"B", "C"}));
        List modules2 = store.put("A", Arrays.asList(new String[]{"C", "D"}));
        List modulesD  = store.getListOfModules("D");
        
        assertNull(modules1);
        
        assertNotNull(modules2);
        assertEquals(2, modules2.size());
        assertTrue(modules2.contains("C"));
        assertTrue(modules2.contains("B"));
        
        assertEquals(1, modulesD.size());
        assertTrue(modulesD.contains("A"));
    }
    
}
