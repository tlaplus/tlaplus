package tlc2.tool;

import org.junit.Ignore;

/** NestedBase variant of the EXCEPT @ regression. */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1521")
public class Github1521FTest extends Github1521SemanticsTestCase {

	public Github1521FTest() {
		super("F");
	}
}
