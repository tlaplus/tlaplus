package org.lamport.tla.toolbox.tool.tlc.output.source;

import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;

/**
 * Marks a TLC output region
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCRegion extends TypedRegion implements ITypedRegion
{
    public static final String TAG = "__tlc_tag";

    private int messageCode;
    private int severity;

    public TLCRegion(int offset, int length)
    {
        this(offset, length, TAG);
    }

    public TLCRegion(int offset, int length, String type)
    {
        super(offset, length, type);
    }

    public final int getMessageCode()
    {
        return messageCode;
    }

    public final void setMessageCode(int messageCode)
    {
        this.messageCode = messageCode;
    }

    public final int getSeverity()
    {
        return severity;
    }

    public final void setSeverity(int severity)
    {
        this.severity = severity;
    }
}
