/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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

package tlc2.module;

import java.io.File;
import java.lang.reflect.Field;

public class BuiltInModuleHelper {
	
	public static final String BUNDLE_ID = "org.lamport.tlatools";

	public static final String STANDARD_MODULES = "StandardModules";
	public static final String STANDARD_MODULES_PATH = File.separator + "tla2sany" + File.separator;
	
	private BuiltInModuleHelper() {
		// no instantiation
	}
	
	public static boolean isBuiltInModule(Class<?> clazz) {
        try {
			// Compare serialVersionUID because a user is allowed to override a
			// built-in module. Thus, the name alone does not uniquely identify
			// a built-in class.
			final Field field = clazz.getField("serialVersionUID");
			if (field != null) {
				final long value = field.getLong(null);
				if (clazz == AnySet.class && value == AnySet.serialVersionUID) {
					return true;
				} else if (clazz == Bags.class && value == Bags.serialVersionUID) {
					return true;
				} else if (clazz == FiniteSets.class && value == FiniteSets.serialVersionUID) {
					return true;
				} else if (clazz == Integers.class && value == Integers.serialVersionUID) {
					return true;
				} else if (clazz == Naturals.class && value == Naturals.serialVersionUID) {
					return true;
				} else if (clazz == Sequences.class && value == Sequences.serialVersionUID) {
					return true;
				} else if (clazz == Strings.class && value == Strings.serialVersionUID) {
					return true;
				} else if (clazz == TLC.class && value == TLC.serialVersionUID) {
					return true;
				} else if (clazz == TransitiveClosure.class && value == TransitiveClosure.serialVersionUID) {
					return true;
				} else if (clazz == Randomization.class && value == Randomization.serialVersionUID) {
					return true;
				} else if (clazz == Json.class && value == Json.serialVersionUID) {
					return true;
				} else if (clazz == TLCExt.class && value == TLCExt.serialVersionUID) {
					return true;
				} else if (clazz == TLCGetSet.class && value == TLCGetSet.serialVersionUID) {
					return true;
				} else if (clazz == TLCEval.class && value == TLCEval.serialVersionUID) {
					return true;
				}
				// TODO Add Toolbox.class here too should Toolbox.tla module ever get a module
				// override.
			}
		} catch (SecurityException e) {
			return false;
		} catch (NoSuchFieldException e) {
			return false;
		} catch (IllegalArgumentException e) {
			return false;
		} catch (IllegalAccessException e) {
			return false;
		}
        return false;
	}
}
