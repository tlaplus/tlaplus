package tlc2.module;
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

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;

import com.cognitect.transit.TransitFactory;
import com.cognitect.transit.Reader;
import com.cognitect.transit.MapReader;
import com.cognitect.transit.ArrayReader;
import com.cognitect.transit.ArrayReadHandler;
import com.cognitect.transit.Writer;
import com.cognitect.transit.WriteHandler;
import com.cognitect.transit.ReadHandler;
import com.cognitect.transit.SPI.ReaderSPI;

import tlc2.overrides.TLAPlusOperator;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnLambdaValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfFcnsValue;
import tlc2.value.impl.SetOfRcdsValue;
import tlc2.value.impl.SetOfTuplesValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.SubsetValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * Module overrides for operators to read and write transit.
 */
public class Transit {
	
	public static final long serialVersionUID = 20220619L;

    private static Map<Class, WriteHandler<?,?>> customHandlers = new HashMap<Class, WriteHandler<?,?>>(){{        
        put(TupleValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "array"; }
            @Override
            public Object rep(Object o) { return Arrays.asList(((TupleValue)o).elems); }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(RecordValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "map"; }
            @Override
            public Object rep(Object o) {
                RecordValue record = ((RecordValue)o);
                HashMap<UniqueString, Value> map = new HashMap<UniqueString, Value>();
                IntStream.range(0, record.size()).forEach(i -> map.put(record.names[i], record.values[i]));;
                return map; 
            }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(UniqueString.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "s"; }
            @Override
            public Object rep(Object o) { return ((UniqueString)o).toString(); }
            @Override
            public String stringRep(Object o) { return (String)rep(o); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(IntValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "i"; }
            @Override
            public Object rep(Object o) { return ((IntValue)o).val; }
            @Override
            public String stringRep(Object o) { return String.valueOf(rep(o)); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(StringValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "s"; }
            @Override
            public Object rep(Object o) { return ((StringValue)o).val.toString(); }
            @Override
            public String stringRep(Object o) { return (String)rep(o); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(ModelValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "s"; }
            @Override
            public Object rep(Object o) { return ((ModelValue)o).val.toString(); }
            @Override
            public String stringRep(Object o) { return (String)rep(o); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(BoolValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "?"; }
            @Override
            public Object rep(Object o) { return ((BoolValue)o).val; }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(FcnRcdValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) {
                FcnRcdValue value = (FcnRcdValue)o;
                if (isValidSequence(value)) {
                    return "array";
                } else {
                    return "map";
                }                
            }
            @Override
            public Object rep(Object o) { 
                FcnRcdValue value = (FcnRcdValue)o;
                if (isValidSequence(value)) {
                    return getArrayNode(value);
                } else {
                    return getObjectNode(value);
                }
            }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });        

        put(SetEnumValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "set"; }
            @Override
            public Object rep(Object o) { 
                SetEnumValue value = (SetEnumValue)o;
                value.normalize();
                return new HashSet<>(Arrays.asList(value.elems.toArray())); 
            }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(SubsetValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "set"; }
            @Override
            public Object rep(Object o) { 
                SetEnumValue value = (SetEnumValue) ((SetOfRcdsValue)o).toSetEnum();
                value.normalize();
                return new HashSet<>(Arrays.asList(value.elems.toArray())); 
            }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(SetOfTuplesValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "set"; }
            @Override
            public Object rep(Object o) { 
                SetEnumValue value = (SetEnumValue) ((SetOfTuplesValue)o).toSetEnum();
                value.normalize();
                return new HashSet<>(Arrays.asList(value.elems.toArray())); 
            }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(SetOfFcnsValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "set"; }
            @Override
            public Object rep(Object o) { 
                SetEnumValue value = (SetEnumValue) ((SetOfFcnsValue)o).toSetEnum();
                value.normalize();
                return new HashSet<>(Arrays.asList(value.elems.toArray())); 
            }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(SubsetValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "set"; }
            @Override
            public Object rep(Object o) { 
                SetEnumValue value = (SetEnumValue) ((SubsetValue)o).toSetEnum();
                value.normalize();
                return new HashSet<>(Arrays.asList(value.elems.toArray())); 
            }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });

        put(IntervalValue.class, new WriteHandler() {
            @Override
            public String tag(Object o) { return "set"; }
            @Override
            public Object rep(Object o) { 
                SetEnumValue value = (SetEnumValue) ((IntervalValue)o).toSetEnum();
                value.normalize();
                return new HashSet<>(Arrays.asList(value.elems.toArray())); 
            }
            @Override
            public String stringRep(Object o) { return rep(o).toString(); }
            @Override
            public WriteHandler getVerboseHandler() { return this; }
        });
    }};

    private static Map<String, ReadHandler<?, ?>> customReadHandlers = new HashMap<String, ReadHandler<?, ?>>() {{
        put("set", new ArrayReadHandler<HashSet<Object>, SetEnumValue, Object, Object>() {
           @Override
           public SetEnumValue fromRep(Object o) {
               HashSet<Value> set = new HashSet<Value>((ArrayList<Value>)o);
               return new SetEnumValue(set.toArray(new Value[set.size()]), true);
           }

           @Override
           public ArrayReader<HashSet<Object>, SetEnumValue, Object> arrayReader() {
               return new SetBuilder();
           }
        });           
    }};

    public static class MapBuilder implements MapReader<Map<Object, Object>, Map<Object, Object>, Object, Object> {
        @Override
        public Map<Object, Object> init() {
            return new HashMap<Object, Object>();
        }

        @Override
        public Map<Object, Object> init(int size) {
            return new HashMap<Object, Object>();
        }

        @Override
        public Map add(Map<Object, Object> m, Object k, Object val) {
            m.put(getValueKey((String) k), getValueObject(val));
            return m;
        }

        @Override
        public Map<Object, Object> complete(Map<Object, Object> m) {
            return m;
        }
    }

    public static class ArrayBuilder implements ArrayReader<List<Object>, List<Object>, Object> {
        @Override
        public List<Object> init() {
            return new ArrayList<>();
        }

        @Override
        public List<Object> init(int size) {
            return new ArrayList<>(size);
        }

        @Override
        public List<Object> add(List<Object> v, Object item) {
            v.add(getValueObject(item));
            return v;
        }

        @Override
        public List<Object> complete(List<Object> m) {
            return m;
        }
    }
    
    public static class SetBuilder implements ArrayReader<HashSet<Object>, SetEnumValue, Object> {
        @Override
        public HashSet<Object> init() {
            return new HashSet<Object>();
        }

        @Override
        public HashSet<Object> init(int size) {
            return new HashSet<Object>();
        }

        @Override
        public HashSet<Object> add(HashSet<Object> v, Object item) {
            v.add(getValueObject(item));
            return v;
        }

        @Override
        public SetEnumValue complete(HashSet<Object> m) {
            return new SetEnumValue(m.toArray(new Value[m.size()]), true);
        }
    }

  /**
   * Deserializes a tuple of separated TRANSIT chunks from the given path.
   *
   * @param path the TRANSIT file path
   * @return a tuple of TRANSIT values
   */
  @TLAPlusOperator(identifier = "ndTransitDeserialize", module = "Transit", warn = false)
  public static IValue ndDeserialize(final StringValue path) throws IOException {
    InputStream in = new FileInputStream(path.val.toString());
    Reader reader = TransitFactory.reader(TransitFactory.Format.MSGPACK, in, customReadHandlers);
    ((ReaderSPI) reader).setBuilders(new MapBuilder(), new ArrayBuilder());    

    List<IValue> values = new ArrayList<>();    
    try { 
        while (true) {        
            values.add((IValue)getValueObject(reader.read()));        
        }
    } catch (Exception e) {
    }
    return new TupleValue(values.toArray(new Value[0]));
  }

  /**
   * Deserializes a tuple of *plain* TRANSIT values from the given path.
   *
   * @param path the TRANSIT file path
   * @return a tuple of TRANSIT values
   */
  @TLAPlusOperator(identifier = "TransitDeserialize", module = "Transit", warn = false)
  public static IValue deserialize(final StringValue path) throws IOException {
    InputStream in = new FileInputStream(path.val.toString());
    Reader reader = TransitFactory.reader(TransitFactory.Format.MSGPACK, in, customReadHandlers);
    ((ReaderSPI) reader).setBuilders(new MapBuilder(), new ArrayBuilder());
    return (IValue)getValueObject(reader.read());
  }

  /**
   * Serializes a tuple of values to separated TRANSIT chunks.
   *
   * @param path  the file to which to write the values
   * @param v the values to write
   * @return a boolean value indicating whether the serialization was successful
   */
  @TLAPlusOperator(identifier = "ndTransitSerialize", module = "Transit", warn = false)
  public synchronized static BoolValue ndSerialize(final StringValue path, final Value v) throws IOException {
    TupleValue value = (TupleValue) v.toTuple();
    
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    Writer w = TransitFactory.writer(TransitFactory.Format.MSGPACK, out, TransitFactory.writeHandlerMap(customHandlers));
    for (Value el : value.elems) {
        w.write(el);
    }
    
    File file = new File(path.val.toString());
    if (file.getParentFile() != null) {file.getParentFile().mkdirs();} // Cannot create parent dir for relative path.
    try (BufferedOutputStream os = new BufferedOutputStream(new FileOutputStream(new File(path.val.toString())))) {
    	os.write(out.toByteArray());    	
    }
    return BoolValue.ValTrue;
  }

  /**
   * Serializes value to TRANSIT.
   *
   * @param path  the file to which to write the values
   * @param value the values to write
   * @return a boolean value indicating whether the serialization was successful
   */
  @TLAPlusOperator(identifier = "TransitSerialize", module = "Transit", warn = false)
  public synchronized static BoolValue serialize(final StringValue path, final Value value) throws IOException {   
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    Writer w = TransitFactory.writer(TransitFactory.Format.MSGPACK, out, TransitFactory.writeHandlerMap(customHandlers));
    w.write(value);    

    File file = new File(path.val.toString());
    if (file.getParentFile() != null) {file.getParentFile().mkdirs();} // Cannot create parent dir for relative path.
    try (BufferedOutputStream os = new BufferedOutputStream(new FileOutputStream(new File(path.val.toString())))) {
    	os.write(out.toByteArray());    	
    }
    return BoolValue.ValTrue;
  }

  private static Object getValueObject(Object o) {
    if (o instanceof Map) {
        return getValue((Map) o);
    } else if (o instanceof List) {
        return getValue((List) o);
    } else if (o instanceof Long) {
        return getValue((Long) o);
    } else if (o instanceof Boolean) {
        return getValue((Boolean) o);
    } else if (o instanceof String) {
        return getValue((String) o);
    } else {
        return o;
    }
  }

  private static Value getValue(Map o) {
    return new RecordValue((HashMap)o);
  }

  private static Value getValue(List o) {
    ArrayList<Value> list = (ArrayList<Value>)o;
    Value[] values = new Value[list.size()];
    IntStream.range(0, list.size()).forEach(i -> values[i] = (Value)list.get(i));                
    return new TupleValue(values);
  }

  private static Value getValue(Long o) {
    return IntValue.gen(o.intValue());
  }

  private static Value getValue(Boolean o) {
    return new BoolValue(o);
  }
  
  private static Value getValue(String o) {
    return new StringValue(o);
  }

  private static UniqueString getValueKey(String o) {
    return UniqueString.of(o);
  }
  
  private static boolean isValidSequence(FcnRcdValue value) {
    final Value[] domain = value.getDomainAsValues();
    for (Value d : domain) {
      if (!(d instanceof IntValue)) {
        return false;
      }
    }
    value.normalize();
    for (int i = 0; i < domain.length; i++) {
      if (((IntValue) domain[i]).val != (i + 1)) {
        return false;
      }
    }
    return true;
  }

  private static HashMap<Object, Value> getObjectNode(FcnRcdValue value) {
    HashMap<Object, Value> map = new HashMap<Object, Value>();
    IntStream.range(0, value.size()).forEach(i -> map.put(value.domain[i], value.values[i]));;    
    return map;
  }
  
  private static List<Value> getArrayNode(FcnRcdValue value) {
    value.normalize();
    return Arrays.asList(value.values);
  }
}
