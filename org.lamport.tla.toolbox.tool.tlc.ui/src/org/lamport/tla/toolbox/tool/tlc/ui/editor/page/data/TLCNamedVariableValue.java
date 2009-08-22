package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

/**
 * Represents named values
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCNamedVariableValue extends TLCVariableValue
{
   private String name;
   
   TLCNamedVariableValue(String name, TLCVariableValue value)
   {
       this.name = name;
       this.value = value;
   }
   
   public String getName()
   {
       return name;
   }
   
   public String toString()
   {
       return value.toString();
   }
}
