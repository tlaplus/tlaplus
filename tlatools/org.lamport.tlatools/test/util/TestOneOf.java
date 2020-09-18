package util;

import static org.junit.Assert.assertEquals;
import org.junit.Test;

public class TestOneOf
{
	private static class A { public final int value = 1; }
	
	private static class B { public final int value = 2;}
	
	private static class C { public final int value = 3; }
	
	@Test
	public void testMap()
	{
		A objA = new A();
		OneOf<A,B,C> o = OneOf.first(objA);
		int result = o.map(
				(a) -> {return a.value;},
				(b) -> {return b.value;},
				(c) -> {return c.value;});
		assertEquals(1, result);
		
		B objB = new B();
		o = OneOf.second(objB);
		result = o.map(
				(a) -> {return a.value;},
				(b) -> {return b.value;},
				(c) -> {return c.value;});
		assertEquals(2, result);
		
		C objC = new C();
		o = OneOf.third(objC);
		result = o.map(
				(a) -> {return a.value;},
				(b) -> {return b.value;},
				(c) -> {return c.value;});
		assertEquals(3, result);
	}
}
