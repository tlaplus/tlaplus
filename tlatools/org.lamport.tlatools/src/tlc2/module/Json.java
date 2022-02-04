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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;

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
 * Module overrides for operators to read and write JSON.
 */
public class Json {
	
	public static final long serialVersionUID = 20210223L;

  /**
   * Encodes the given value as a JSON string.
   *
   * @param value the value to encode
   * @return the JSON string value
   */
  @TLAPlusOperator(identifier = "ToJson", module = "Json", warn = false)
  public static StringValue toJson(final IValue value) throws IOException {
    return new StringValue(getNode(value).toString());
  }

  /**
   * Encodes the given value as a JSON array string.
   *
   * @param value the value to encode
   * @return the JSON array string value
   */
  @TLAPlusOperator(identifier = "ToJsonArray", module = "Json", warn = false)
  public static StringValue toJsonArray(final IValue value) throws IOException {
    return new StringValue(getArrayNode(value).toString());
  }

  /**
   * Encodes the given value as a JSON object string.
   *
   * @param value the value to encode
   * @return the JSON object string value
   */
  @TLAPlusOperator(identifier = "ToJsonObject", module = "Json", warn = false)
  public static StringValue toJsonObject(final IValue value) throws IOException {
    return new StringValue(getObjectNode(value).toString());
  }

  /**
   * Deserializes a tuple of newline delimited JSON values from the given path.
   *
   * @param path the JSON file path
   * @return a tuple of JSON values
   */
  @TLAPlusOperator(identifier = "ndJsonDeserialize", module = "Json", warn = false)
  public static IValue ndDeserialize(final StringValue path) throws IOException {
    List<Value> values = new ArrayList<>();
    try (BufferedReader reader = new BufferedReader(new FileReader(new File(path.val.toString())))) {
      String line = reader.readLine();
      while (line != null) {
        JsonElement node = JsonParser.parseString(line);
        values.add(getValue(node));
        line = reader.readLine();
      }
    }
    return new TupleValue(values.toArray(new Value[0]));
  }

  /**
   * Deserializes a tuple of *plain* JSON values from the given path.
   *
   * @param path the JSON file path
   * @return a tuple of JSON values
   */
  @TLAPlusOperator(identifier = "JsonDeserialize", module = "Json", warn = false)
  public static IValue deserialize(final StringValue path) throws IOException {
    JsonElement node = JsonParser.parseReader(new FileReader(new File(path.val.toString())));
    return getValue(node);
  }

  /**
   * Serializes a tuple of values to newline delimited JSON.
   *
   * @param path  the file to which to write the values
   * @param value the values to write
   * @return a boolean value indicating whether the serialization was successful
   */
  @TLAPlusOperator(identifier = "ndJsonSerialize", module = "Json", warn = false)
  public synchronized static BoolValue ndSerialize(final StringValue path, final Value v) throws IOException {
	TupleValue value = (TupleValue) v.toTuple();
    File file = new File(path.val.toString());
    if (file.getParentFile() != null) {file.getParentFile().mkdirs();} // Cannot create parent dir for relative path.
    try (BufferedWriter writer = new BufferedWriter(new FileWriter(new File(path.val.toString())))) {
        for (int i = 0; i < value.elems.length; i++) {
            writer.write(getNode(value.elems[i]).toString() + "\n");
          }
    }
    return BoolValue.ValTrue;
  }

  /**
   * Serializes a tuple of values to newline delimited JSON.
   *
   * @param path  the file to which to write the values
   * @param value the values to write
   * @return a boolean value indicating whether the serialization was successful
   */
  @TLAPlusOperator(identifier = "JsonSerialize", module = "Json", warn = false)
  public synchronized static BoolValue serialize(final StringValue path, final Value v) throws IOException {
	TupleValue value = (TupleValue) v.toTuple();
    File file = new File(path.val.toString());
    if (file.getParentFile() != null) {file.getParentFile().mkdirs();} // Cannot create parent dir for relative path.
    try (BufferedWriter writer = new BufferedWriter(new FileWriter(new File(path.val.toString())))) {
    	writer.write("[\n");
		for (int i = 0; i < value.elems.length; i++) {
			writer.write(getNode(value.elems[i]).toString());
			if (i < value.elems.length - 1) {
				// No dangling "," after last element.
				writer.write(",\n");
			}
		}
    	writer.write("\n]\n");
    }
    return BoolValue.ValTrue;
  }

  /**
   * Recursively converts the given value to a {@code JsonElement}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getNode(IValue value) throws IOException {
    if (value instanceof RecordValue) {
      return getObjectNode((RecordValue) value);
    } else if (value instanceof TupleValue) {
      return getArrayNode((TupleValue) value);
    } else if (value instanceof StringValue) {
      return new JsonPrimitive(((StringValue) value).val.toString());
    } else if (value instanceof ModelValue) {
      return new JsonPrimitive(((ModelValue) value).val.toString());
    } else if (value instanceof IntValue) {
      return new JsonPrimitive(((IntValue) value).val);
    } else if (value instanceof BoolValue) {
      return new JsonPrimitive(((BoolValue) value).val);
    } else if (value instanceof FcnRcdValue) {
      return getObjectNode((FcnRcdValue) value);
    } else if (value instanceof FcnLambdaValue) {
      return getObjectNode((FcnRcdValue) ((FcnLambdaValue) value).toFcnRcd());
    } else if (value instanceof SetEnumValue) {
      return getArrayNode((SetEnumValue) value);
    } else if (value instanceof SetOfRcdsValue) {
      return getArrayNode((SetEnumValue) ((SetOfRcdsValue) value).toSetEnum());
    } else if (value instanceof SetOfTuplesValue) {
      return getArrayNode((SetEnumValue) ((SetOfTuplesValue) value).toSetEnum());
    } else if (value instanceof SetOfFcnsValue) {
      return getArrayNode((SetEnumValue) ((SetOfFcnsValue) value).toSetEnum());
    } else if (value instanceof SubsetValue) {
      return getArrayNode((SetEnumValue) ((SubsetValue) value).toSetEnum());
    } else if (value instanceof IntervalValue) {
      return getArrayNode((SetEnumValue) ((IntervalValue) value).toSetEnum());
    } else {
      throw new IOException("Cannot convert value: unsupported value type " + value.getClass().getName());
    }
  }

  /**
   * Returns a boolean indicating whether the given value is a valid sequence.
   *
   * @param value the value to check
   * @return indicates whether the value is a valid sequence
   */
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

  /**
   * Recursively converts the given value to an {@code JsonObject}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getObjectNode(IValue value) throws IOException {
    if (value instanceof RecordValue) {
      return getObjectNode((RecordValue) value);
    } else if (value instanceof TupleValue) {
      return getObjectNode((TupleValue) value);
    } else if (value instanceof FcnRcdValue) {
      return getObjectNode((FcnRcdValue) value);
    } else if (value instanceof FcnLambdaValue) {
      return getObjectNode((FcnRcdValue) ((FcnLambdaValue) value).toFcnRcd());
    } else {
      throw new IOException("Cannot convert value: unsupported value type " + value.getClass().getName());
    }
  }

  /**
   * Converts the given record value to a {@code JsonObject}, recursively converting values.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getObjectNode(FcnRcdValue value) throws IOException {
    if (isValidSequence(value)) {
      return getArrayNode(value);
    }

    final Value[] domain = value.getDomainAsValues();
    JsonObject jsonObject = new JsonObject();
    for (int i = 0; i < domain.length; i++) {
      Value domainValue = domain[i];
      if (domainValue instanceof StringValue) {
        jsonObject.add(((StringValue) domainValue).val.toString(), getNode(value.values[i]));
      } else {
        jsonObject.add(domainValue.toString(), getNode(value.values[i]));
      }
    }
    return jsonObject;
  }

  /**
   * Converts the given record value to an {@code JsonObject}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getObjectNode(RecordValue value) throws IOException {
    JsonObject jsonObject = new JsonObject();
    for (int i = 0; i < value.names.length; i++) {
      jsonObject.add(value.names[i].toString(), getNode(value.values[i]));
    }
    return jsonObject;
  }

  /**
   * Converts the given tuple value to an {@code JsonObject}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getObjectNode(TupleValue value) throws IOException {
    JsonObject jsonObject = new JsonObject();
    for (int i = 0; i < value.elems.length; i++) {
      jsonObject.add(String.valueOf(i), getNode(value.elems[i]));
    }
    return jsonObject;
  }

  /**
   * Recursively converts the given value to an {@code JsonArray}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getArrayNode(IValue value) throws IOException {
    if (value instanceof TupleValue) {
      return getArrayNode((TupleValue) value);
    } else if (value instanceof FcnRcdValue) {
      return getArrayNode((FcnRcdValue) value);
    } else if (value instanceof FcnLambdaValue) {
      return getArrayNode((FcnRcdValue) ((FcnLambdaValue) value).toFcnRcd());
    } else if (value instanceof SetEnumValue) {
      return getArrayNode((SetEnumValue) value);
    } else if (value instanceof SetOfRcdsValue) {
      return getArrayNode((SetEnumValue) ((SetOfRcdsValue) value).toSetEnum());
    } else if (value instanceof SetOfTuplesValue) {
      return getArrayNode((SetEnumValue) ((SetOfTuplesValue) value).toSetEnum());
    } else if (value instanceof SetOfFcnsValue) {
      return getArrayNode((SetEnumValue) ((SetOfFcnsValue) value).toSetEnum());
    } else if (value instanceof SubsetValue) {
      return getArrayNode((SetEnumValue) ((SubsetValue) value).toSetEnum());
    } else if (value instanceof IntervalValue) {
      return getArrayNode((SetEnumValue) ((IntervalValue) value).toSetEnum());
    } else {
      throw new IOException("Cannot convert value: unsupported value type " + value.getClass().getName());
    }
  }

  /**
   * Converts the given tuple value to an {@code JsonArray}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getArrayNode(TupleValue value) throws IOException {
    JsonArray jsonArray = new JsonArray(value.elems.length);
    for (int i = 0; i < value.elems.length; i++) {
      jsonArray.add(getNode(value.elems[i]));
    }
    return jsonArray;
  }

  /**
   * Converts the given record value to an {@code JsonArray}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getArrayNode(FcnRcdValue value) throws IOException {
    if (!isValidSequence(value)) {
      return getObjectNode(value);
    }

    value.normalize();
    JsonArray jsonArray = new JsonArray(value.values.length);
    for (int i = 0; i < value.values.length; i++) {
      jsonArray.add(getNode(value.values[i]));
    }
    return jsonArray;
  }

  /**
   * Converts the given tuple value to an {@code JsonArray}.
   *
   * @param value the value to convert
   * @return the converted {@code JsonElement}
   */
  private static JsonElement getArrayNode(SetEnumValue value) throws IOException {
    value.normalize();
    Value[] values = value.elems.toArray();
    JsonArray jsonArray = new JsonArray(values.length);
    for (int i = 0; i < values.length; i++) {
      jsonArray.add(getNode(values[i]));
    }
    return jsonArray;
  }

  /**
   * Recursively converts the given {@code JsonElement} to a TLC value.
   *
   * @param node the {@code JsonElement} to convert
   * @return the converted value
   */
  private static Value getValue(JsonElement node) throws IOException {
    if (node.isJsonArray()) {
      return getTupleValue(node);
    }
    else if (node.isJsonObject()) {
      return getRecordValue(node);
    }
    else if (node.isJsonPrimitive()) {
      JsonPrimitive primitive = node.getAsJsonPrimitive();
      if (primitive.isNumber()) {
        return IntValue.gen(primitive.getAsInt());
      }
      else if (primitive.isBoolean()) {
        return new BoolValue(primitive.getAsBoolean());
      }
      else if (primitive.isString()) {
        return new StringValue(primitive.getAsString());
      }
    }
    else if (node.isJsonNull()) {
      return null;
    }
    throw new IOException("Cannot convert value: unsupported JSON value " + node.toString());
  }

  /**
   * Converts the given {@code JsonElement} to a tuple.
   *
   * @param node the {@code JsonElement} to convert
   * @return the tuple value
   */
  private static TupleValue getTupleValue(JsonElement node) throws IOException {
    List<Value> values = new ArrayList<>();
    JsonArray jsonArray = node.getAsJsonArray();
    for (int i = 0; i < jsonArray.size(); i++) {
      values.add(getValue(jsonArray.get(i)));
    }
    return new TupleValue(values.toArray(new Value[0]));
  }

  /**
   * Converts the given {@code JsonElement} to a record.
   *
   * @param node the {@code JsonElement} to convert
   * @return the record value
   */
  private static RecordValue getRecordValue(JsonElement node) throws IOException {
    List<UniqueString> keys = new ArrayList<>();
    List<Value> values = new ArrayList<>();
    Iterator<Map.Entry<String, JsonElement>> iterator = node.getAsJsonObject().entrySet().iterator();
    while (iterator.hasNext()) {
      Map.Entry<String, JsonElement> entry = iterator.next();
      keys.add(UniqueString.uniqueStringOf(entry.getKey()));
      values.add(getValue(entry.getValue()));
    }
    return new RecordValue(keys.toArray(new UniqueString[0]), values.toArray(new Value[0]), false);
  }
}
