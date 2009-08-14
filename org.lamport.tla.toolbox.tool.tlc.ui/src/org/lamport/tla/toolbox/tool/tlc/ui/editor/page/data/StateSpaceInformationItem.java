package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;

import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * Representation of the state space progress item 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StateSpaceInformationItem
{
    private Date time;
    private int diameter;
    private int foundStates;
    private int distinctStates;
    private int leftStates;

    /**
     * @param time
     * @param diameter
     * @param foundStates
     * @param distinctStates
     * @param leftStates
     */
    private StateSpaceInformationItem(Date time, int diameter, int foundStates, int distinctStates, int leftStates)
    {
        super();
        this.time = time;
        this.diameter = diameter;
        this.foundStates = foundStates;
        this.distinctStates = distinctStates;
        this.leftStates = leftStates;
    }

    public final Date getTime()
    {
        return time;
    }

    public final void setTime(Date time)
    {
        this.time = time;
    }

    public final int getDiameter()
    {
        return diameter;
    }

    public final void setDiameter(int diameter)
    {
        this.diameter = diameter;
    }

    public final int getFoundStates()
    {
        return foundStates;
    }

    public final void setFoundStates(int foundStates)
    {
        this.foundStates = foundStates;
    }

    public final int getDistinctStates()
    {
        return distinctStates;
    }

    public final void setDistinctStates(int distinctStates)
    {
        this.distinctStates = distinctStates;
    }

    public final int getLeftStates()
    {
        return leftStates;
    }

    public final void setLeftStates(int leftStates)
    {
        this.leftStates = leftStates;
    }

    /**
     * @param outputMessage
     * @return
     */
    public static StateSpaceInformationItem parse(String outputMessage)
    {
        // TODO support formats of SIMULATOR and DFID
        // "Progress(23) at 2009-08-07 08:20:02: 1604317 states generated, 421523 distinct states found, 109513 states left on queue."
        int[] i = { outputMessage.indexOf(OB), outputMessage.indexOf(AT), outputMessage.indexOf(COLON),
                outputMessage.indexOf(GENERATED), outputMessage.indexOf(DISTINCT), outputMessage.indexOf(LEFT) };

        for (int j = 0; j < i.length; j++)
        {
            if (i[j] == -1)
            {
                TLCUIActivator.logError("Error reading progress information", new IllegalArgumentException(
                        outputMessage + " is in wrong format"));
                return null;
            }
        }
        
        try
        {
            return new StateSpaceInformationItem(SDF.parse(outputMessage.substring(i[1] + AT.length(), i[2])), Integer
                    .parseInt(outputMessage.substring(i[0] + OB.length(), i[1])), Integer
                    .parseInt(outputMessage.substring(i[2] + COLON.length(), i[3])), Integer
                    .parseInt(outputMessage.substring(i[3] + GENERATED.length(), i[4])), Integer
                    .parseInt(outputMessage.substring(i[4] + DISTINCT.length(), i[5])));
        } catch (NumberFormatException e)
        {
            TLCUIActivator.logError("Error reading progress information", e);
        } catch (ParseException e)
        {
            TLCUIActivator.logError("Error reading progress information", e);
        }
        return null;
    }

    public final static SimpleDateFormat SDF = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");

    public final static String OB = "(";
    public final static String AT = ") at ";
    public final static String COLON = ": ";
    public final static String GENERATED = " states generated, ";
    public final static String DISTINCT = " distinct states found, ";
    public final static String LEFT = " states left on queue.";

}
