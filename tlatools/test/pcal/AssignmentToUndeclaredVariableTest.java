package pcal;

import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;

import org.junit.Test;

import util.ToolIO;

public class AssignmentToUndeclaredVariableTest extends PCalTest {
	@Test
	public void procedure() throws IOException {
		assertNull(trans.runMe(new String[] {"-nocfg", 
							writeTempFile("AssignmentToUndeclaredVariableTest", 
				"---- MODULE algo ----\n" + 
				"CONSTANT c\n" + 
				"(*\n" + 
				"--algorithm algo {\n" + 
				"  variables v, w;\n" + 
				"    procedure Proc1() \n" + 
				"      {p1 : v := 23;\n" + 
				"            c := 42 }\n" + 
				" {\n" +
				"  i: call Proc1();\n" + // Assignment to constant
				" }\n" + 
				"}*)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.toString(ToolIO.getAllMessages()),
				Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Assignment to undeclared variable c\n"
					+ "    at line 8, column 13.\n"));
	}
	
	@Test
	public void process() throws IOException {
		assertNull(trans.runMe(new String[] {"-nocfg", 
							writeTempFile("AssignmentToUndeclaredVariableTest", 
				"---- MODULE algo ----\n" + 
				"CONSTANT c\n" + 
				"(*\n" + 
				"--algorithm algo {\n" + 
				"  variables v, w;\n" + 
				"  process (proc \\in {1,2})\n" + 
				"    variable loc\n" + 
				" {\n" +
				"   lbl1: loc := 42;\n" +
				"   lbl2: v := 23;\n" +
				"   lbl3: w := 174;\n" +
				"   lbl4: c := \"fail\";\n" + // Assignment to constant
				" }\n" + 
				"}*)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.toString(ToolIO.getAllMessages()),
				Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Assignment to undeclared variable c\n"
					+ "    at line 12, column 10.\n"));
	}
	
	@Test
	public void multiAssignment() throws IOException {
		assertNull(trans.runMe(new String[] {"-nocfg", 
							writeTempFile("AssignmentToUndeclaredVariableTest", 
				"---- MODULE algo ----\n" + 
				"CONSTANT c\n" + 
				"(*\n" + 
				"--algorithm algo {\n" + 
				"  variables v, w;\n" + 
				" {\n" +
				"  v := 42 || w := 23;\n" +
				"  v := 42 || c := 23;\n" + // Assignment to constant
				" }\n" + 
				"}*)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.toString(ToolIO.getAllMessages()),
				Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Assignment to undeclared variable c\n"
					+ "    at line 8, column 11.\n"));
	}

	@Test
	public void macro() throws IOException {
		assertNull(trans.runMe(new String[] {"-nocfg", 
							writeTempFile("AssignmentToUndeclaredVariableTest", 
				"---- MODULE algo ----\n" + 
				"CONSTANT c\n" + 
				"(*\n" + 
				"--algorithm algo {\n" + 
				"  variables v;\n" + 
				"  macro Mac() { v := \"pmac\";\n c := 42; }\n" + 
				" {\n" +
				"  Mac();\n" + // Assignment to constant
				" }\n" + 
				"}*)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.toString(ToolIO.getAllMessages()),
				Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Assignment to undeclared variable c\n"
					+ "    at line 7, column 2 of macro called at line 9, column 3.\n"));
	}
	
	@Test
	public void macroParam() throws IOException {
		assertNull(trans.runMe(new String[] {"-nocfg", 
							writeTempFile("AssignmentToUndeclaredVariableTest", 
				"---- MODULE algo ----\n" + 
				"CONSTANT c\n" + 
				"(*\n" + 
				"--algorithm algo {\n" + 
				"  variables v;\n" + 
				"  macro Mac2(p) { p := \"pmac\"}\n" + 
				" {\n" +
				"  lbl1: Mac2(v);\n" +
				"  lbl2: Mac2(c);\n" + // Assignment to constant
				" }\n" + 
				"}*)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Assignment to undeclared variable c\n"
					+ "    at line 6, column 19 of macro called at line 9, column 9.\n"));
	}
	
	@Test
	public void boundIdentifier() throws IOException {
		assertNull(trans.runMe(new String[] {"-nocfg", 
							writeTempFile("AssignmentToUndeclaredVariableTest", 
				"---- MODULE algo ----\n" + 
				"CONSTANT c\n" + 
				"(*\n" + 
				"--algorithm algo\n" + 
				"  variables v;\n" + 
				"begin\n" +
				"   with n \\in {1,2,3} do\n" +
				"      v := n;\n" + 
				"      n := 42;\n" + // Assignment to bound identifier!
				"   end with;" +
				"end algorithm\n" + 
				" *)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Assignment to undeclared variable n\n"
					+ "    at line 9, column 7.\n"));
	}
	
	@Test
	public void constant() throws IOException {
		assertNull(trans.runMe(new String[] {"-nocfg", 
			writeTempFile("AssignmentToUndeclaredVariableTest", 
				"---- MODULE algo ----\n" + 
				"CONSTANT c\n" + 
				"(*\n" + 
				"--algorithm algo\n" + 
				"  variables v;\n" + 
				"begin\n" + 
				"   v := 23;\n" + 
				"   c := 42;\n" + // Assignment to constant! 
				"end algorithm\n" + 
				" *)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Assignment to undeclared variable c\n"
					+ "    at line 8, column 4.\n"));
	}
	
	private static String writeTempFile(String filename, String content) throws IOException {
		final Path path = Files.createTempFile(filename, ".tla");
		Files.write(path, content.getBytes());
		
		final File file = path.toFile();
		file.deleteOnExit();
		return file.getAbsolutePath();
	}
}
