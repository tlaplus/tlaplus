package org.lamport.tla.toolbox.tool.tlc.output.data;

import junit.framework.Assert;
import junit.framework.TestCase;

import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue.InputPair;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue.VariableValueParseException;

public class TLCVariableValueTest extends TestCase
{
    public void testGetNextChar()
    {
        String test = "1234567";
        try
        {
            Assert.assertEquals('4', TLCVariableValue.getNextChar(new InputPair(test, 3)));
        } catch (VariableValueParseException e)
        {
            Assert.fail();
        }
    }

    public void testGetNextCharIncrement()
    {
        String test = "1234567";
        InputPair input = new InputPair(test, 3);
        try
        {
            Assert.assertEquals('4', TLCVariableValue.getNextChar(input));
            Assert.assertEquals(4, input.offset);
        } catch (VariableValueParseException e)
        {
            Assert.fail();
        }
    }

    public void testGetNextChar2()
    {
        String test = "1234567";
        try
        {
            TLCVariableValue.getNextChar(new InputPair(test, 7));
            Assert.fail();
        } catch (VariableValueParseException e)
        {
            Assert.assertTrue(true);
        }
    }

    public void testGetNextChar3()
    {
        String test = "";
        try
        {
            TLCVariableValue.getNextChar(new InputPair(test, 6));
            Assert.fail();
        } catch (VariableValueParseException e)
        {
            Assert.assertTrue(true);
        }
    }

    public void testParseValueSimple()
    {
        String[] test = { "abc", "12", "   12", "  -12", "1212.212"  , "\"\\\"xyz\"" };
        String[] result = { "abc", "12", "12", "-12", "1212.212", "\"\\\"xyz\"" };
        for (int i = 0; i < test.length; i++)
        {
            try
            {
                InputPair pair = new InputPair(test[i], 0);
                TLCVariableValue parseValue = TLCVariableValue.innerParse(pair);
                Assert.assertTrue(parseValue instanceof TLCSimpleVariableValue);
                Assert.assertEquals(result[i], parseValue.value);
                Assert.assertEquals(test[i].length(), pair.offset);
            } catch (VariableValueParseException e)
            {
                Assert.fail("Error running the test " + i);
            }
        }
    }

    public void testParseValueSet()
    {
        String[] test = { "{}", "{12}", "{12  ,  23}" };
        String[][] result = { new String[0], new String[] { "12" }, new String[] { "12", "23" } };
        for (int i = 0; i < test.length; i++)
        {
            try
            {
                TLCVariableValue parseValue = TLCVariableValue.innerParse(new InputPair(test[i], 0));
                Assert.assertTrue(parseValue instanceof TLCSetVariableValue);
                TLCSetVariableValue value = (TLCSetVariableValue) parseValue;
                TLCVariableValue[] elements = value.getElements();
                for (int j = 0; j < elements.length; j++)
                {
                    Assert.assertEquals(result[i][j], elements[j].value);
                }
            } catch (VariableValueParseException e)
            {
                Assert.fail("Error running the test " + i);
            }
        }
    }

    public void testParseValueSeq()
    {
        String[] test = { "<<>>", "<<12>>", "<<12  ,  23>>" };
        String[][] result = { new String[0], new String[] { "12" }, new String[] { "12", "23" } };
        for (int i = 0; i < test.length; i++)
        {
            try
            {
                TLCVariableValue parseValue = TLCVariableValue.innerParse(new InputPair(test[i], 0));
                Assert.assertTrue(parseValue instanceof TLCSequenceVariableValue);
                TLCSequenceVariableValue value = (TLCSequenceVariableValue) parseValue;
                TLCVariableValue[] elements = value.getElements();
                for (int j = 0; j < elements.length; j++)
                {
                    Assert.assertEquals(result[i][j], (
                            (TLCVariableValue) ((TLCFcnElementVariableValue) elements[j]).value).value);
                    Assert.assertEquals(true,
                            ((TLCFcnElementVariableValue) elements[j]).getFrom().value.equals(""+(j+1))) ;
                }
            } catch (VariableValueParseException e)
            {
                Assert.fail("Error running the test " + i);
            }
        }
    }

    public void testParseValueFcn()
    {
        String[] test = { "(1 :> a @@ 2 :> b)" };
        String[][][] result = { {{"1", "a"}, {"2", "b"}} };
        for (int i = 0; i < test.length; i++)
        {
            try
            {
                TLCVariableValue parseValue = TLCVariableValue.innerParse(new InputPair(test[i], 0));
                Assert.assertTrue(parseValue instanceof TLCFunctionVariableValue);
                TLCFunctionVariableValue value = (TLCFunctionVariableValue) parseValue;
                TLCFcnElementVariableValue[] elements = value.getFcnElements();
                for (int j = 0; j < elements.length; j++)
                {
                    Assert.assertEquals(result[i][j][0], elements[j].from.toString());
                    Assert.assertEquals(result[i][j][1], elements[j].value.toString());
                }
            } catch (VariableValueParseException e)
            {
                Assert.fail("Error running the test " + i);
            }
        }
    }

    public void testParseValueSet2()
    {
        String test = "{{12}}";
        
            try
            {
                TLCVariableValue parseValue = TLCVariableValue.innerParse(new InputPair(test, 0));
                Assert.assertTrue(parseValue instanceof TLCSetVariableValue);
                
                TLCSetVariableValue value = (TLCSetVariableValue) parseValue;
                TLCVariableValue[] elements = value.getElements();
                
                for (int j = 0; j < elements.length; j++)
                {
                    Assert.assertTrue(elements[j] instanceof TLCSetVariableValue);
                    TLCSetVariableValue child = (TLCSetVariableValue) elements[j];
                    TLCVariableValue[] elements2 = child.getElements();
                    for (int k = 0; k < elements2.length; k++) 
                    {
                        Assert.assertEquals("12", elements2[k].value);
                    } 
                }
            } catch (VariableValueParseException e)
            {
                Assert.fail();
            }
    }

}
