/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

package tlc2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class TestMPRecorder extends tlc2.output.MPRecorder {
	private final Map<Integer, List<Object>> records = new HashMap<Integer, List<Object>>();
	
	public void record(int code, Object... objects) {
		if(!records.containsKey(code)) {
			records.put(code, new ArrayList<Object>());
		}
		records.get(code).add(objects);
	}

	public boolean recorded(int code) {
		return records.containsKey(code);
	}

	public List<Object> getRecords(int code) {
		return records.get(code);
	}

	// This is a best effort implementation that only checks the first
	// elements of the nested records and contained arrays
	public boolean recordedWithStringValue(int code, String str) {
		try {
			return recordedWithStringValueAt(code, str, 0);
		} catch (Exception e) {
			return false;
		}
	}

	public boolean recordedWithStringValueAt(int code, String str, int idx) {
		try {
			Object object = records.get(code).get(0);
			if (object instanceof String[]) {
				String[] strs = (String[]) object;
				return strs[idx].equals(str);
			} else if (object instanceof String) {
				return object.equals(str);
			}
			return false;
		} catch (Exception e) {
			return false;
		}
	}

	public boolean recordedWithStringValues(int code, String... strings) {
		int i = 0;
		for (String string : strings) {
			if (!recordedWithStringValueAt(code, string, i++)) {
				return false;
			}
			return true;
		}
		return false;
	}
}
