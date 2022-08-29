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

import tlc2.output.EC;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class TestMPRecorder implements tlc2.output.IMessagePrinterRecorder {
    private final Map<Integer, List<Object>> records = new HashMap<>();

    @Override
    public void record(final int code, final Object... objects) {
        if (!records.containsKey(code)) {
            records.put(code, new ArrayList<>());
        }
        records.get(code).add(objects);
    }

    public boolean recorded(final int code) {
        return records.containsKey(code);
    }

    public List<Object> getRecords(final int code) {
        return records.get(code);
    }

    private List<Object> getRecordsOrDefault(final int code, final List<Object> defaultValue) {
        return records.getOrDefault(code, defaultValue);
    }

    public int getRecordAsInt(final int code) {
        return Integer.parseInt(((String[]) records.get(code).get(0))[0]);
    }

    public List<String[]> getRecordAsStringArray(final int code) {
        final List<Object> l = records.getOrDefault(code, new ArrayList<>());

        final List<String[]> strs = new ArrayList<>(l.size());
        for (final Object o : l) {
            strs.add((String[]) o);
        }
        return strs;
    }

    // This is a best effort implementation that only checks the first
    // elements of the nested records and contained arrays
    public boolean recordedWithStringValue(final int code, final String str) {
        try {
            return recordedWithStringValueAt(code, str, 0);
        } catch (final Exception e) {
            return false;
        }
    }

    public boolean recordedWithSubStringValue(final int code, final String substring) {
        try {
            final Object object = records.get(code).get(0);
            if (object instanceof final String[] strs) {
                for (final String string : strs) {
                    if (string.contains(substring)) {
                        return true;
                    }
                }
                return false;
            } else if (object instanceof String) {
                return ((String) object).contains(substring);
            }
            return false;
        } catch (final Exception e) {
            return false;
        }
    }

    public boolean recordedWithStringValueAt(final int code, final String str, final int idx) {
        try {
            final Object object = records.get(code).get(0);
            if (object instanceof final String[] strs) {
                return strs[idx].equals(str);
            } else if (object instanceof String) {
                return object.equals(str);
            }
            return false;
        } catch (final Exception e) {
            return false;
        }
    }

    public boolean recordedWithStringValueAt(final Object codeRecord, final String str, final int idx) {
        try {
            if (codeRecord instanceof final String[] strs) {
                return strs[idx].equals(str);
            } else if (codeRecord instanceof String) {
                return codeRecord.equals(str);
            }
            return false;
        } catch (final Exception e) {
            return false;
        }
    }

    public boolean recordedWithStringValues(final int code, final String... strings) {
        var codeRecords = records.get(code);

        for (var codeRecord : codeRecords) {
            int i = 0;
            for (final String string : strings) {
                if (!recordedWithStringValueAt(codeRecord, string, i)) {
                    break;
                }

                i++;
            }

            if (i == strings.length) {
                return true;
            }
        }

        return false;
    }

    public List<Coverage> getActionCoverage() {
        final List<Object> init = getRecordsOrDefault(EC.TLC_COVERAGE_INIT, new ArrayList<>(0));
        final List<Object> next = getRecordsOrDefault(EC.TLC_COVERAGE_NEXT, new ArrayList<>(0));
        final List<Object> prop = getRecordsOrDefault(EC.TLC_COVERAGE_PROPERTY, new ArrayList<>(0));
        final List<Object> con = getRecordsOrDefault(EC.TLC_COVERAGE_CONSTRAINT, new ArrayList<>(0));
        init.addAll(next);
        init.addAll(prop);
        init.addAll(con);

        return init.stream().map(o -> (String[]) o).map(Coverage::new).filter(Coverage::isAction)
                .collect(Collectors.toList());
    }

    public List<Coverage> getZeroCoverage() {
        return getCoverage(EC.TLC_COVERAGE_VALUE, (Predicate<? super Coverage>) Coverage::isZero);
    }

    public List<Coverage> getNonZeroCoverage() {
        return getCoverage(EC.TLC_COVERAGE_VALUE, (Predicate<? super Coverage>) o -> !o.isZero());
    }

    public List<Coverage> getCostCoverage() {
        return getCoverage(EC.TLC_COVERAGE_VALUE_COST, (Predicate<? super Coverage>) o -> !o.isZero());
    }

    private List<Coverage> getCoverage(final int code, final Predicate<? super Coverage> p) {
        final List<Object> coverages = getRecordsOrDefault(code, new ArrayList<>(0));
        return coverages.stream().map(o -> (String[]) o).map(Coverage::new).filter(p)
                .collect(Collectors.toList());
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        final StringBuilder buf = new StringBuilder(records.size());
        for (final Integer key : records.keySet()) {
            final List<Object> list = records.get(key);
            for (final Object elem : list) {
                if (elem instanceof final String[] strs) {
                    for (final String s : strs) {
                        buf.append(key);
                        buf.append(" -> ");
                        buf.append(s);
                        buf.append("\n");
                    }
                } else if (elem instanceof String) {
                    buf.append(key);
                    buf.append(" -> ");
                    buf.append(elem);
                    buf.append("\n");
                }
            }
        }
        return buf.toString();
    }

    public static class Coverage {
        private final String line;
        private final long count;
        private final long cost;
        //TODO Take level into account in comparison!
        private final int level;
        private final boolean isAction;

        public Coverage(final String[] line) {
            this.isAction = line[0].startsWith("<");
            this.line = line[0].replace("|", "").trim();
            this.level = line[0].length() - this.line.length();
            if (line.length == 1) {
                this.count = -1;
                this.cost = -1;
            } else if (line.length == 2) {
                this.count = Long.parseLong(line[1].trim());
                this.cost = -1;
            } else if (line.length == 3) {
                this.count = Long.parseLong(line[1].trim());
                this.cost = Long.parseLong(line[2].trim());
            } else {
                throw new IllegalArgumentException();
            }
        }

        public boolean isZero() {
            return count == 0L;
        }

        public boolean isCoverage() {
            return !isAction;
        }

        public boolean isCost() {
            return cost >= 0;
        }

        public boolean isAction() {
            return isAction;
        }

        @Override
        public String toString() {
            return "Coverage [line=" + line + ", count=" + count + ", cost=" + cost + "]";
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + (int) (count ^ (count >>> 32));
            result = prime * result + (int) (cost ^ (cost >>> 32));
            result = prime * result + ((line == null) ? 0 : line.hashCode());
            return result;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            final Coverage other = (Coverage) obj;
            if (count != other.count)
                return false;
            if (cost != other.cost)
                return false;
            if (line == null) {
                return other.line == null;
            } else return line.equals(other.line);
        }
    }
}
