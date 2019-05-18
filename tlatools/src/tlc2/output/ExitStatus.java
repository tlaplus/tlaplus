package tlc2.output;

import static tlc2.output.EC.*;

public class ExitStatus
{

    public static final int fromErrorCode(int errorCode)
    {
        final int exitStatus;
        switch (errorCode) {
            
            case NO_ERROR:
                exitStatus = 0;
                break;

            // System errors
            case SYSTEM_CHECKPOINT_RECOVERY_CORRUPT:
            case SYSTEM_DISK_IO_ERROR_FOR_FILE:
            case SYSTEM_DISKGRAPH_ACCESS:
            case SYSTEM_ERROR_CLEANING_POOL:
            case SYSTEM_ERROR_READING_POOL:
            case SYSTEM_ERROR_READING_STATES:
            case SYSTEM_ERROR_WRITING_POOL:
            case SYSTEM_ERROR_WRITING_STATES:
            case SYSTEM_FILE_NULL:
            case SYSTEM_INDEX_ERROR:
            case SYSTEM_INTERRUPTED:
            case SYSTEM_METADIR_CREATION_ERROR:
            case SYSTEM_METADIR_EXISTS:
            case SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT:
            case SYSTEM_OUT_OF_MEMORY:
            case SYSTEM_STACK_OVERFLOW:
            case SYSTEM_STREAM_EMPTY:
            case SYSTEM_UNABLE_NOT_RENAME_FILE:
            case SYSTEM_UNABLE_TO_OPEN_FILE:
                exitStatus = 2;
                break;

            // Violations
            case TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR:
            case TLC_INVARIANT_VIOLATED_BEHAVIOR:
            case TLC_INVARIANT_VIOLATED_INITIAL:
            case TLC_INVARIANT_VIOLATED_LEVEL:
            case TLC_PROPERTY_VIOLATED_INITIAL:
            case TLC_TEMPORAL_PROPERTY_VIOLATED:
                exitStatus = 3;
                break;
        
            default:
                exitStatus = 255;
        }

        assert exitStatus >= 0 && exitStatus <= 255;
        return exitStatus;
    }
}