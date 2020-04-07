/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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

import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

/**
 * @see MethodValue.
 */
@Retention(RUNTIME)
@Target(METHOD)
public @interface TLAPlusCallable {

	/**
	 * @return The identifier of a TLA+ state or action predicate. 
	 */
	String definition();

	/**
	 * @return The name of the TLA+ module declaring the definition above.
	 */
	String module();

	/**
	 * @return The minimum level that will be assigned to the OpDefNode that
	 *         represents the EvaluatingValue in the semantic graph. Unless
	 *         the actual level checking in Spec.getLevelBound assigns a
	 *         greater value, the OpDefNode is a constant-level expression if
	 *         0 causing it to be eagerly evaluated in 
	 *         SpecProcessor.processConstantDefns.
	 * @see tla2sany.semantic.LevelNode.getLevel()
	 * @see tlc2.tool.impl.Spec.getLevelBound(SemanticNode, Context)
	 * @see tlc2.value.impl.EvaluatingValue
	 * @see tlc2.tool.impl.SpecProcessor.processConstantDefns()
	 */
	int minLevel() default 0;
	
	/**
	 * @return true if a warning should be printed when a EV cannot be mapped to the
	 *         given TLA+ definition in module.
	 * @see Evaluation#definition()
	 * @see Evaluation#module()
	 */
	boolean warn() default true;
}
