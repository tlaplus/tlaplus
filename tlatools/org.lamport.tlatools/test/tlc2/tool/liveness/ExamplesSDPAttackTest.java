/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved. 
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
package tlc2.tool.liveness;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

public class ExamplesSDPAttackTest extends ModelCheckerTestCase {

	public ExamplesSDPAttackTest() {
		super("MC", "examples/SDP_Verification/SDP_Attack_Spec", new String[] { "-lncheck", "final" }, ExitStatus.VIOLATION_SAFETY);
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	// Repeated record values used across multiple states.
	private static final String SPA_AUTH_SET = "{ [ MsgID |-> \"SPA_AUTH\",\n" + "    sIP |-> 11,\n"
			+ "    sPort |-> 1024,\n" + "    dIP |-> 12,\n" + "    dPort |-> 8000,\n" + "    ClientID |-> 1,\n"
			+ "    Tstamp |-> 0,\n" + "    SvrIP |-> 58,\n" + "    SvrPort |-> 124,\n" + "    HMAC |-> 238,\n"
			+ "    Type |-> \"User\" ] }";

	private static final String SPA_AUTH_SEQ = "<< [ MsgID |-> \"SPA_AUTH\",\n" + "     sIP |-> 11,\n"
			+ "     sPort |-> 1024,\n" + "     dIP |-> 12,\n" + "     dPort |-> 8000,\n" + "     ClientID |-> 1,\n"
			+ "     Tstamp |-> 0,\n" + "     SvrIP |-> 58,\n" + "     SvrPort |-> 124,\n" + "     HMAC |-> 238,\n"
			+ "     Type |-> \"User\" ] >>";

	private static final String USR_SYN_SET = "{ [ sIP |-> 11,\n" + "    sPort |-> 1025,\n" + "    dIP |-> 22,\n"
			+ "    dPort |-> 80,\n" + "    Type |-> \"User\",\n" + "    Flg |-> \"TCP_SYN\" ] }";

	private static final String USR_SYN_SEQ = "<< [ sIP |-> 11,\n" + "     sPort |-> 1025,\n" + "     dIP |-> 22,\n"
			+ "     dPort |-> 80,\n" + "     Type |-> \"User\",\n" + "     Flg |-> \"TCP_SYN\" ] >>";

	private static final String FW_CTL_ADD_SEQ = "<< [ op |-> \"Add\",\n" + "     Rule |->\n"
			+ "         [ sIP |-> 11,\n" + "           sPort |-> 65536,\n" + "           dIP |-> 22,\n"
			+ "           dPort |-> 80,\n" + "           protocol |-> \"TCP\",\n"
			+ "           action |-> \"Accept\" ] ] >>";

	private static final String ACL_WILD = "{ [ sIP |-> 11,\n" + "    sPort |-> 65536,\n" + "    dIP |-> 22,\n"
			+ "    dPort |-> 80,\n" + "    protocol |-> \"TCP\",\n" + "    action |-> \"Accept\" ] }";

	private static final String ACL_TWO = "{ [ sIP |-> 11,\n" + "    sPort |-> 2024,\n" + "    dIP |-> 22,\n"
			+ "    dPort |-> 80,\n" + "    protocol |-> \"TCP\",\n" + "    action |-> \"Accept\" ],\n"
			+ "  [ sIP |-> 11,\n" + "    sPort |-> 65536,\n" + "    dIP |-> 22,\n" + "    dPort |-> 80,\n"
			+ "    protocol |-> \"TCP\",\n" + "    action |-> \"Accept\" ] }";

	private static final String ATK_SYN_SENT = "{ [ sIP |-> 11,\n" + "    sPort |-> 2024,\n" + "    dIP |-> 22,\n"
			+ "    dPort |-> 80,\n" + "    State |-> \"SYN_SENT\",\n" + "    AuthID |-> 65535 ] }";

	private static final String ATK_SYN_SEQ = "<< [ sIP |-> 11,\n" + "     sPort |-> 2024,\n" + "     dIP |-> 22,\n"
			+ "     dPort |-> 80,\n" + "     Type |-> \"Attacker\",\n" + "     Flg |-> \"TCP_SYN\" ] >>";

	private static final String ATK_ACK_SEQ = "<< [ sIP |-> 11,\n" + "     sPort |-> 2024,\n" + "     dIP |-> 22,\n"
			+ "     dPort |-> 80,\n" + "     Type |-> \"Attacker\",\n" + "     Flg |-> \"TCP_ACK\" ] >>";

	private static String state(String capDataMsg, String sChannel, String sTCPLinkSet, String uState,
			String dropPackets, String fwDataChannel, String aCounter, String aChannel, String aTCPLinkSet,
			String sdpSucSession, String dataKnowledge, String spoofSession, String agedRuleSet, String fwCtlChannel,
			String uTstamp, String sniffCount, String aclRuleSet, String uTCPLinkSet, String authKnowledge,
			String uAuthSession, String authChannel) {
		return "/\\ CapDataMsg = " + capDataMsg + "\n" + "/\\ sChannel = " + sChannel + "\n" + "/\\ sTCPLinkSet = "
				+ sTCPLinkSet + "\n" + "/\\ uSvrInfo = [IP |-> 22, Port |-> 80]\n" + "/\\ uState = \"" + uState + "\"\n"
				+ "/\\ DropPackets = " + dropPackets + "\n" + "/\\ FwState = \"Work\"\n" + "/\\ ReplayCount = 0\n"
				+ "/\\ aState = \"Listen\"\n" + "/\\ CapAuthMsg = {}\n" + "/\\ FwDataChannel = " + fwDataChannel + "\n"
				+ "/\\ SDPSvrState = \"Work\"\n" + "/\\ aCounter = " + aCounter + "\n" + "/\\ aChannel = " + aChannel
				+ "\n" + "/\\ aTCPLinkSet = " + aTCPLinkSet + "\n" + "/\\ SDPSucSession = " + sdpSucSession + "\n"
				+ "/\\ aIP = 11\n" + "/\\ uChannel = <<>>\n" + "/\\ Account = {[Key |-> 44, ClientID |-> 1]}\n"
				+ "/\\ DataKnowledge = " + dataKnowledge + "\n" + "/\\ SpoofSession = " + spoofSession + "\n"
				+ "/\\ uID = 1\n" + "/\\ ReplaySession = {}\n" + "/\\ sState = \"Listen\"\n" + "/\\ Key = 44\n"
				+ "/\\ uIP = 11\n" + "/\\ SpoofCount = 0\n" + "/\\ AgedRuleSet = " + agedRuleSet + "\n"
				+ "/\\ FwCtlChannel = " + fwCtlChannel + "\n" + "/\\ sSvrInfo = [IP |-> 22, Port |-> 80]\n"
				+ "/\\ uTstamp = " + uTstamp + "\n" + "/\\ sniffCount = " + sniffCount + "\n" + "/\\ AclRuleSet = "
				+ aclRuleSet + "\n" + "/\\ uSDPSvrInfo = [IP |-> 12, Port |-> 8000]\n" + "/\\ aSession = {}\n"
				+ "/\\ uTCPLinkSet = " + uTCPLinkSet + "\n" + "/\\ AuthKnowledge = " + authKnowledge + "\n"
				+ "/\\ SDPSvrInfo = [IP |-> 12, Port |-> 8000]\n" + "/\\ uAuthSession = " + uAuthSession + "\n"
				+ "/\\ AuthChannel = " + authChannel;
	}

	private static final String USR_TCP = "{[sIP |-> 11, sPort |-> 1025, dIP |-> 22, dPort |-> 80, State |-> \"SYN_SENT\"]}";

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1103", "526", "175"));
		assertFalse(recorder.recorded(EC.GENERAL));

		assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, "DataAccessSafeLaw"));

		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<>(11);

		// State 1: <Initial predicate>
		expectedTrace.add(state("{}", "<<>>", "{}", "Start_Auth", "{}", "<<>>", "0", "<<>>", "{}", "{}", "{}", "{}",
				"{}", "<<>>", "0", "0", "{}", "{}", "{}", "{}", "<<>>"));

		// State 2: <UsrCommitSpaAuth>
		expectedTrace.add(state("{}", "<<>>", "{}", "Auth_End", "{}", "<<>>", "0", "<<>>", "{}", "{}", "{}", "{}", "{}",
				"<<>>", "1", "0", "{}", "{}", "{}", SPA_AUTH_SET, SPA_AUTH_SEQ));

		// State 3: <UsrConnectSvr>
		expectedTrace.add(state("{}", "<<>>", "{}", "Connecting", "{}", USR_SYN_SEQ, "0", "<<>>", "{}", "{}", "{}",
				"{}", "{}", "<<>>", "1", "0", "{}", USR_TCP, "{}", SPA_AUTH_SET, SPA_AUTH_SEQ));

		// State 4: <SDPSvrProcSpaAuth>
		expectedTrace.add(state("{}", "<<>>", "{}", "Connecting", "{}", USR_SYN_SEQ, "0", "<<>>", "{}", SPA_AUTH_SET,
				"{}", "{}", "{}", FW_CTL_ADD_SEQ, "1", "0", "{}", USR_TCP, "{}", SPA_AUTH_SET, "<<>>"));

		// State 5: <AttackerSniffDataChannel>
		expectedTrace
				.add(state(USR_SYN_SET, "<<>>", "{}", "Connecting", "{}", USR_SYN_SEQ, "0", "<<>>", "{}", SPA_AUTH_SET,
						USR_SYN_SET, "{}", "{}", FW_CTL_ADD_SEQ, "1", "1", "{}", USR_TCP, "{}", SPA_AUTH_SET, "<<>>"));

		// State 6: <FwProcEndPointAccess>
		expectedTrace.add(
				state(USR_SYN_SET, "<<>>", "{}", "Connecting", USR_SYN_SET, "<<>>", "0", "<<>>", "{}", SPA_AUTH_SET,
						USR_SYN_SET, "{}", "{}", FW_CTL_ADD_SEQ, "1", "1", "{}", USR_TCP, "{}", SPA_AUTH_SET, "<<>>"));

		// State 7: <FwProcAclCfg>
		expectedTrace.add(
				state(USR_SYN_SET, "<<>>", "{}", "Connecting", USR_SYN_SET, "<<>>", "0", "<<>>", "{}", SPA_AUTH_SET,
						USR_SYN_SET, "{}", "{}", "<<>>", "1", "1", ACL_WILD, USR_TCP, "{}", SPA_AUTH_SET, "<<>>"));

		// State 8: <AttackerProbeSvr>
		expectedTrace.add(state(USR_SYN_SET, "<<>>", "{}", "Connecting", USR_SYN_SET, ATK_SYN_SEQ, "1", "<<>>",
				ATK_SYN_SENT, SPA_AUTH_SET, "{}", "{}", "{}", "<<>>", "1", "1", ACL_WILD, USR_TCP, "{}", SPA_AUTH_SET,
				"<<>>"));

		// State 9: <FwProcEndPointAccess>
		expectedTrace.add(state(USR_SYN_SET, ATK_SYN_SEQ, "{}", "Connecting", USR_SYN_SET, "<<>>", "1", "<<>>",
				ATK_SYN_SENT, SPA_AUTH_SET, "{}", "{}", "{}", "<<>>", "1", "1", ACL_TWO, USR_TCP, "{}", SPA_AUTH_SET,
				"<<>>"));

		// State 10: <ServerRcvTCPSyn>
		final String sTCPLink10 = "{ [ sIP |-> 22,\n" + "    sPort |-> 80,\n" + "    dIP |-> 11,\n"
				+ "    dPort |-> 2024,\n" + "    Type |-> \"Attacker\",\n" + "    State |-> \"SYN_RCVD\" ] }";
		final String aChannel10 = "<< [ sIP |-> 22,\n" + "     sPort |-> 80,\n" + "     dIP |-> 11,\n"
				+ "     dPort |-> 2024,\n" + "     Type |-> \"Attacker\",\n" + "     Flg |-> \"TCP_SYN_ACK\" ] >>";
		expectedTrace.add(state(USR_SYN_SET, "<<>>", sTCPLink10, "Connecting", USR_SYN_SET, "<<>>", "1", aChannel10,
				ATK_SYN_SENT, SPA_AUTH_SET, "{}", "{}", "{}", "<<>>", "1", "1", ACL_TWO, USR_TCP, "{}", SPA_AUTH_SET,
				"<<>>"));

		// State 11: <AttackerRcvSynAck>
		final String atkEstablished = "{ [ sIP |-> 11,\n" + "    sPort |-> 2024,\n" + "    dIP |-> 22,\n"
				+ "    dPort |-> 80,\n" + "    State |-> \"ESTABLISHED\",\n" + "    AuthID |-> 65535 ] }";
		expectedTrace.add(state(USR_SYN_SET, "<<>>", sTCPLink10, "Connecting", USR_SYN_SET, ATK_ACK_SEQ, "1", "<<>>",
				atkEstablished, SPA_AUTH_SET, "{}", "{}", "{}", "<<>>", "1", "1", ACL_TWO, USR_TCP, "{}", SPA_AUTH_SET,
				"<<>>"));

		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
	}
}
