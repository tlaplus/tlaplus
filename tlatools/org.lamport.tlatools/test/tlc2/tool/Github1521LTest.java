package tlc2.tool;

import org.junit.Ignore;

/** Enabled variant of the EXCEPT @ regression. */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1521")
public class Github1521LTest extends Github1521SemanticsTestCase {

	public Github1521LTest() {
		super("L");
	}
}
