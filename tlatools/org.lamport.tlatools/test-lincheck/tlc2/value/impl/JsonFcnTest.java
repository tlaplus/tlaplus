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
 * The function f == (1 :> 10 @@ 2 :> 20 @@ m :> 30), whose domain is not
 * normalized, for the untyped model value m. A worker that evaluates ToJson(f)
 * or ToJsonArray(f) while another worker sorts f must still get
 * {"1":10,"2":20,"m":30} or {"m":30,"1":10,"2":20}, because f is not a
 * sequence. Sorting moves m, which precedes every integer, to the front of the
 * domain. If Json reads the domain of f without a snapshot to check that it
 * has only integers, it may read 1 before the sort and 2 and 1 after it, take f
 * for a sequence, and fail when it casts m to an integer.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class JsonFcnTest extends ValueLincheckTestCase {

	static {
		internResults(ValueLincheckTestCase::unsortedMixedFcn, Json::toJson);
		internResults(ValueLincheckTestCase::unsortedMixedFcn, Json::toJsonArray);
	}

	private final FcnRcdValue fcn = unsortedMixedFcn();

	@Override
	protected Value value() {
		return fcn;
	}

	@Operation
	public String toJson() throws IOException {
		return Json.toJson(fcn).val.toString();
	}

	@Operation
	public String toJsonArray() throws IOException {
		return Json.toJsonArray(fcn).val.toString();
	}

	@Test
	public void fingerPrintAndToJson() {
		modelCheckingParallel("fingerPrint", "toJson");
	}

	@Test
	public void fingerPrintAndToJsonArray() {
		modelCheckingParallel("fingerPrint", "toJsonArray");
	}
}
