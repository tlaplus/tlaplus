/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
package tlc2.value.impl;

import java.io.IOException;

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tlc2.module.Json;

/**
 * The record r == [f3 |-> 30, f1 |-> 10, f2 |-> 20], whose fields are not
 * normalized. A worker that evaluates ToJson(r) while another worker sorts r
 * must still get {"f3":30,"f1":10,"f2":20} or {"f1":10,"f2":20,"f3":30}. If
 * Json#toJson reads the names and the values of r one after the other, without
 * a lock, it may pair a name with another field's value, or see a field twice.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class JsonRecordTest extends ValueLincheckTestCase {

	static {
		internResults(ValueLincheckTestCase::unsortedRcd, Json::toJson);
	}

	private final RecordValue rcd = unsortedRcd();

	@Override
	protected Value value() {
		return rcd;
	}

	@Operation
	public String toJson() throws IOException {
		return Json.toJson(rcd).val.toString();
	}

	@Test
	public void fingerPrintAndToJson() {
		modelCheckingParallel("fingerPrint", "toJson");
	}
}
