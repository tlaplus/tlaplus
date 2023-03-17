// Copyright (c) 2023, Oracle and/or its affiliates.

package util;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import tlc2.TLCGlobals;
import tlc2.output.EC;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Date;

public class FileUtilTest {

    /**
     * This test writes to the filesystem.  To avoid clutter, it creates a temporary directory before
     * each test and deletes it after the test.
     */
    private Path tmpDir;

    /**
     * This test modifies the global variable {@link TLCGlobals#metaDir}.  To avoid test order dependence,
     * it saves the original value before each test and restores it at the end.
     */
    private String oldMetaDir;

    @Before
    public void setUp() throws IOException {
        tmpDir = Files.createTempDirectory("tla-tests");
        oldMetaDir = TLCGlobals.metaDir;
    }

    @After
    public void tearDown() {
        TLCGlobals.metaDir = oldMetaDir;
        FileUtil.deleteDir(tmpDir.toFile(), true);
    }

    @Test
    public void testReturnFromCheckpoint() {
        // If the fromChkpt arg is provided, then it is returned as-is, even if it does not exist.
        Assert.assertEquals(
                "abc",
                FileUtil.makeMetaDir(tmpDir.toString(), "abc"));
    }

    @Test
    public void testDuplicateStateDirCreation() {
        Date now = new Date();

        // Two calls to makeMetaDir with the same date should both succeed and return different directories.
        String path1 = FileUtil.makeMetaDir(now, tmpDir.toString(), null);
        String path2 = FileUtil.makeMetaDir(now, tmpDir.toString(), null);
        Assert.assertNotEquals(path1, path2);

        // Both directories should be in tmpDir/TLCGlobals.metaRoot.
        Assert.assertEquals(tmpDir.resolve(TLCGlobals.metaRoot), Paths.get(path1).getParent());
        Assert.assertEquals(tmpDir.resolve(TLCGlobals.metaRoot), Paths.get(path2).getParent());
    }

    @Test
    public void testUseDifferentMetaDir() {
        Date now = new Date();

        TLCGlobals.metaDir = tmpDir.resolve("fizz").resolve("buzz").toString();
        String path = FileUtil.makeMetaDir(now, tmpDir.toString(), null);

        // If {@link TLCGlobals#metaDir} is set, then that directory is created and used as the parent.
        Assert.assertEquals(Paths.get(TLCGlobals.metaDir), Paths.get(path).getParent());
        Assert.assertTrue(Files.isDirectory(Paths.get(path)));
    }

}
