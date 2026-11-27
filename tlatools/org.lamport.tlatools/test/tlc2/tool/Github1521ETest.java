package tlc2.tool;

import org.junit.Ignore;

/** PriorUpdate variant of the EXCEPT @ regression. */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1521")
public class Github1521ETest extends Github1521SemanticsTestCase {

	public Github1521ETest() {
		super("E");
	}
}
