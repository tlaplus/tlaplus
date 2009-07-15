package tla2sany.output;

/**
 * Resolves messages for SANY
 * @author Simon Zambrovski, Leslie Lamport
 * @version $Id$
 */
public class MessageResolver
{
    public static void resolveSANYMessage(StringBuffer b, int errorCode, String[] parameters) 
    {
        switch (errorCode) 
        {
        case SANYCodes.UNKNOWN:
            break;
/*
 * This class is used in the following way to support the replacements of the
 * strings inside of the SANY code. 
 * 
 * Any kind of String used as a message reported to the user should be replaced with
 * the call of the message printer.
 * 
 * The main class for message resolution and printing is called tlc2.output.MP
 * The main class for constants is called tlc2.output.EC
 *  
 * For the usage inside of the SANY, there are two helper classes: tla2sany.output.SANYCodes
 * and tla2sany.output.MessageResolver. During the replacement work these two classes will be used.
 *  
 * Here is an example for usage of non-parameterized messages. Assume we have code like this:
 *  
 * Assert.fail("getLevel called for TheoremNode before levelCheck");
 *  
 * which should be replaced by the call of Assert with the error code. First of all we need to add an additional
 * case in the MessageResolver class resolveSANYMessage() method. For doing this, a new constant is required. 
 * Since all SANY constants are in the SANYCode class we add a line 
 *  
 * public final static int GET_LEVEL_THEOREM_BEFORE_LEVEL_CHECK = 4005;
 *  
 * Important is that all values of the constants start with digit 4 and should be 4-digit code. After the constant 
 * is added we add the case to the switch:
 *  
 * case SANYCodes.GET_LEVEL_THEOREM_BEFORE_LEVEL_CHECK:
 *     b.append("getLevel called for TheoremNode before levelCheck");
 *     break;
 *  
 * After that, we replace the code Assert.fail("getLevel called for TheoremNode before levelCheck"); by
 * Assert.fail(SANYCodes.GET_LEVEL_THEOREM_BEFORE_LEVEL_CHECK); There will be a warning inside of the 
 * class, that SANYCodes can not be resolve, so we add it to the imported classes. In order to do this quickly, 
 * put the cursor into the line with the error, and hit Ctrl + 1. The opened quick assist will propose to add the import...
 * Another acceleration can be achieved by adding the case first and pointing the non-existent constant. Again the error 
 * will appear in the MessageResolver class and the Ctrl + 1 will open the quick assist first proposition will be to add
 * the constant to the SANYCodes. This saves the typing of the name of the constant and the modifier, but you have to put 
 * the value of the constant...
 *  
 * Now assume there is another message in the same class: 
 *   
 * Assert.fail("getLevel called for LabelNode before levelCheck");
 * 
 * The message is actually the same, but instead of TheoremNode it has LabelNode. In order to keep with it you can add another
 * constant, or re-think the semantics of the actual message. So in this case I would change the semantics and rename the 
 * constant to GET_LEVEL_BEFORE_LEVEL_CHECK. Change the code in the case to:
 * case SANYCodes.GET_LEVEL_BEFORE_LEVEL_CHECK:
 *     b.append("getLevel called for %1% before levelCheck");
 *     break;
 * Please note the %1% in the string. This will be replaced by the first parameter. The call will be:
 * Assert.fail(SANYCodes.GET_LEVEL_BEFORE_LEVEL_CHECK, new String[]{"TheoremNode"}); and 
 * Assert.fail(SANYCodes.GET_LEVEL_BEFORE_LEVEL_CHECK, new String[]{"LabelNode"}); respectively. 
 * 
 * There is also a shortcut for writing this: Assert.fail(SANYCodes.GET_LEVEL_BEFORE_LEVEL_CHECK, "LabelNode"); which
 * is a shortcut.
 * 
 * In general, you can insert more %i% into the message and provide the parameters in the String array.  
 * 
 */         
/* **************************************************************************** */
        case SANYCodes.UNIT_TEST: // example of usage
            b.append("Some String with %1% parameter");
            break;
/* **************************************************************************** */
        
            
            
            
            
/* **************************************************************************** */            
        default:
            break;

        }        
    }
}
