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
package tlc2.overrides;

import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Value;

public class UserModuleOverrideAnnotationImpl {

	@TLAPlusOperator(identifier="Get", module="UserModuleOverrideAnnotation")
	public static Value getNumberOne() {
		return BoolValue.ValTrue;
	}
	
	@TLAPlusOperator(identifier="Get2", module="UserModuleOverrideAnnotation")
	public static Value Get2() {
		return BoolValue.ValTrue;
	}
	
	//************ The ones below will cause warnings because they don't match ************//
	
	@TLAPlusOperator(identifier="Get2", module="UserModuleOverrideAnnotation")
	public static Value Get2(Value v1) {
		return BoolValue.ValFalse;
	}

	@TLAPlusOperator(identifier="NoSuchIdentifier", module="UserModuleOverrideAnnotation")
	public static Value noSuchIdentifier() {
		return BoolValue.ValFalse;
	}
	
	@TLAPlusOperator(identifier="Get", module="NoSuchModule")
	public static Value noSuchModule() {
		return BoolValue.ValFalse;
	}
}
