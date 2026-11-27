package tlc2.tool;

import org.junit.Ignore;

/** OperatorArgument variant of the EXCEPT @ regression. */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1521")
public class Github1521ITest extends Github1521SemanticsTestCase {

	public Github1521ITest() {
		super("I");
	}
}
