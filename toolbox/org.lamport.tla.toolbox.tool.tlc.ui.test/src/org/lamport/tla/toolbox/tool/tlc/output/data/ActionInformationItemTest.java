/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.output.data;

import static org.junit.Assert.*;

import org.junit.Test;

public class ActionInformationItemTest {

	@Test
	public void testParseInit() {
		final ActionInformationItem item = ActionInformationItem
				.parseInit("<Init line 13, col 1 to line 14, col 5 of module H>: 3:15", "Model");
		assertNotNull(item);
		assertNull(item.getDefinition());

		assertEquals("H", item.getModule());
		assertEquals("Model", item.getModelName());

		assertEquals("Init", item.getName());
		
		assertEquals(13, item.getModuleLocation().beginLine());
		assertEquals(1, item.getModuleLocation().beginColumn());
		assertEquals(14, item.getModuleLocation().endLine());
		assertEquals(5, item.getModuleLocation().endColumn());

		assertEquals(3, item.getCost());
		assertEquals(15, item.getCount());
	}
	
	@Test
	public void testParseInit2() {
		final ActionInformationItem item = ActionInformationItem
				.parseInit("<Init line 13, col 1 to line 17, col 5 of module H (14 16 15 28)>: 3:15", "Model");
		assertNotNull(item);
		
		assertEquals(14, item.getDefinition().beginLine());
		assertEquals(16, item.getDefinition().beginColumn());
		assertEquals(15, item.getDefinition().endLine());
		assertEquals(28, item.getDefinition().endColumn());

		assertEquals("H", item.getModule());
		assertEquals("Model", item.getModelName());

		assertEquals("Init", item.getName());
		
		assertEquals(13, item.getModuleLocation().beginLine());
		assertEquals(1, item.getModuleLocation().beginColumn());
		assertEquals(17, item.getModuleLocation().endLine());
		assertEquals(5, item.getModuleLocation().endColumn());

		assertEquals(3, item.getCost());
		assertEquals(15, item.getCount());
	}

	@Test
	public void testParseNext() {
		final ActionInformationItem item = ActionInformationItem
				.parseNext("<BandC line 13, col 1 to line 14, col 5 of module H>: 2:15", "Model");
		assertNotNull(item);
		assertNull(item.getDefinition());

		assertEquals("H", item.getModule());
		assertEquals("Model", item.getModelName());

		assertEquals("BandC", item.getName());
		
		assertEquals(13, item.getModuleLocation().beginLine());
		assertEquals(1, item.getModuleLocation().beginColumn());
		assertEquals(14, item.getModuleLocation().endLine());
		assertEquals(5, item.getModuleLocation().endColumn());

		assertEquals(2, item.getCost());
		assertEquals(15, item.getCount());
	}

	@Test
	public void testParseNextWithDefinition() {
		final ActionInformationItem item = ActionInformationItem
				.parseNext("<BandC line 13, col 1 to line 17, col 5 of module H (14 16 15 28)>: 2:15", "Model");
		assertNotNull(item);
		
		assertEquals(14, item.getDefinition().beginLine());
		assertEquals(16, item.getDefinition().beginColumn());
		assertEquals(15, item.getDefinition().endLine());
		assertEquals(28, item.getDefinition().endColumn());

		assertEquals("H", item.getModule());
		assertEquals("Model", item.getModelName());

		assertEquals("BandC", item.getName());
		
		assertEquals(13, item.getModuleLocation().beginLine());
		assertEquals(1, item.getModuleLocation().beginColumn());
		assertEquals(17, item.getModuleLocation().endLine());
		assertEquals(5, item.getModuleLocation().endColumn());

		assertEquals(2, item.getCost());
		assertEquals(15, item.getCount());
	}
}
