package tlc2.tool;

import org.junit.Ignore;

/** NestedPath variant of the EXCEPT @ regression. */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1521")
public class Github1521GTest extends Github1521SemanticsTestCase {

	public Github1521GTest() {
		super("G");
	}
}
