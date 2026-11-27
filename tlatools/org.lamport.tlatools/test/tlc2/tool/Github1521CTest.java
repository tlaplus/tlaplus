package tlc2.tool;

import org.junit.Ignore;

/** Unchanged variant of the EXCEPT @ regression. */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1521")
public class Github1521CTest extends Github1521SemanticsTestCase {

	public Github1521CTest() {
		super("C");
	}
}
