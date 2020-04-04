package org.lamport.tla.toolbox;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.lamport.tla.toolbox.tool.tlc.ui.test.ModelCheckerTest;
import org.lamport.tla.toolbox.ui.handler.CloneModelTest;
import org.lamport.tla.toolbox.ui.handler.RenameSpecHandlerTest;

@RunWith(Suite.class)
@SuiteClasses({
    ModelCheckerTest.class,
    CloneModelTest.class,
    RenameSpecHandlerTest.class
})

public class SmokeTests {}
