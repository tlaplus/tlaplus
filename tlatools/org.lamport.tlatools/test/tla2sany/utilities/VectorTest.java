package tla2sany.utilities;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.List;

import org.junit.Test;

public class VectorTest {

  @Test
  public void containsUsesIdentityComparison() {
    final Vector<String> vector = new Vector<>();
    final String reference = new String("value");
    vector.addElement(reference);

    assertTrue(vector.contains(reference));
    assertFalse(vector.contains(new String("value"))); // equal value, different reference
  }

  @Test
  public void insertElementAtRejectsAppendPosition() {
    final Vector<String> vector = new Vector<>();
    vector.addElement("a");
    vector.addElement("b");

    try {
      vector.insertElementAt("c", 2); // index == size should throw
      fail("Expected ArrayIndexOutOfBoundsException");
    } catch (final ArrayIndexOutOfBoundsException expected) {
      // expected
    }
  }

  @Test
  public void elementsReturnsSnapshot() {
    final Vector<String> vector = new Vector<>();
    vector.addElement("a");
    vector.addElement("b");

    final Enumeration<String> enumeration = vector.elements();
    vector.addElement("c"); // mutate after creating enumeration

    final List<String> snapshot = new ArrayList<>();
    while (enumeration.hasMoreElements()) {
      snapshot.add(enumeration.nextElement());
    }

    assertEquals(Arrays.asList("a", "b"), snapshot);
  }

  @Test
  public void appendNoRepeatsUsesIdentity() {
    final Vector<String> base = new Vector<>();
    final String shared = new String("dup");
    final String equalButDistinct = new String("dup");
    base.addElement(shared);

    final Vector<String> incoming = new Vector<>();
    incoming.addElement(equalButDistinct);
    incoming.addElement(shared);

    base.appendNoRepeats(incoming);

    assertEquals(2, base.size());
    assertSame(shared, base.elementAt(0));
    assertSame(equalButDistinct, base.elementAt(1)); // added because contains checks ==
  }
}
