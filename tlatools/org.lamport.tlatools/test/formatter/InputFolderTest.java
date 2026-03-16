package formatter;

import org.junit.Test;

public class InputFolderTest extends LexiconTest {
    @Test
    public void testPlayground() {
        testSpecFiles("Playground");
    }

    @Test
    public void testFormatHourClock() {
        testSpecFiles("HourClock");
    }

    @Test
    public void testRecordsWithNestedRecordsAndSequences() {
        testSpecFiles("RecordsWithNestedRecordsAndSequences");
    }

    @Test
    public void testIFET() {
        testSpecFiles("IfThenElseTest");
    }

    @Test
    public void testStones() {
        testSpecFiles("Stones");
    }

    @Test
    public void testTowerOfHanoi() {
        testSpecFiles("TowerOfHanoi");
    }

    @Test
    public void testSlush() {
        testSpecFiles("Slush");
    }

    @Test
    public void testAllConstructs() {
        testSpecFiles("AllConstructs");
    }

    @Test
    public void testTransitiveClosure() {
        testSpecFiles("TransitiveClosure");
    }
}
