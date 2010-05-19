package org.lamport.tla.toolbox;

import org.lamport.tla.toolbox.spec.parser.ParseResultBroadcaster;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;

public class ParseResultSpecLifecycleParticipant extends SpecLifecycleParticipant
{

    public ParseResultSpecLifecycleParticipant()
    {
        // TODO Auto-generated constructor stub
    }

    public boolean eventOccured(SpecEvent event)
    {
        if (event.getType() == SpecEvent.TYPE_CLOSE)
        {
            /*
             * We clear any information that the parse result broadcaster
             * has when the spec is closed because the parse result
             * broadcasters saves a map of module names to parse results.
             * These module names are unique within a spec but not unique globally
             * so information in the class should not persist across changes of specs.
             */
            ParseResultBroadcaster.getParseResultBroadcaster().clear();
        }
        return false;
    }

}
