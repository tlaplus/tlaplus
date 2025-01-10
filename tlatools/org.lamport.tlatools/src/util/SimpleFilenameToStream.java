// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, 2025, Oracle and/or its affiliates.
// Last modified on Sat 28 June 2008 at  0:23:49 PST by lamport

package util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;


/**
 * Defines a translation from names to NamedInputStream's that will be
 * used by most tools whose input comes from files.
 * @author simonzam Leslie Lamport, Simon Zambrovski
 * @version $Id$
 */
//SZ Feb 20, 2009: moved to util and fixed bugs

// If a file ``matching'' the module name is found then an instance of
// a stream - NamedInputStream is returned.

// This code contains a special detector trace for the presence of a
// newline in a string. This was a problem with earlier versions of java on PCs.


public class SimpleFilenameToStream implements FilenameToStream {

	public static final String TLA_LIBRARY = "TLA-Library";

	public static final String STANDARD_MODULES_FOLDER = "StandardModules";

	private static final ClassLoader cl = SimpleFilenameToStream.class.getClassLoader();

	private static final String STANDARD_MODULES = "tla2sany"
			+ '/' + STANDARD_MODULES_FOLDER + '/';

  protected final Path tmpDir = FilenameToStream.getTempDirectory();

  /**
   * Locates user (i.e. non-library) files and modules.
   */
  private final ResourceLocator userFileResourceLocator;

  /**
   * Locates standard library files and modules.
   */
  private final ResourceLocator standardLibraryResourceLocator;

  public SimpleFilenameToStream() {
    this((String[])null);
  }

  public SimpleFilenameToStream(final String libraryPath) {
	  this(new String[] {libraryPath});
  }
  
/**
 * August 2014 - TL
 * This constructor was on the interface but was not implemented.
 * Now one can pass additional libraries which will be added to the
 * installation path and instead the path supplied using the system property TLA_LIBRARY
 * (which is being used in the default constructor).
 */
  public SimpleFilenameToStream(String[] anLibraryPaths) {
    userFileResourceLocator = getLibraryPaths(anLibraryPaths);
    standardLibraryResourceLocator = getInstallationBasePath();
  }

  /**
   * Find the TLA+ standard modules.
   *
   * @return a locator for finding the TLA+ standard modules
   */
  private static ResourceLocator getInstallationBasePath() {
    // First search the standard modules installation location, then search the
    // bare classpath.  For historical reasons, modules discovered in both of these
    // locations are considered "library" modules.
    return new SequentialResourceLocator(List.of(
            new ClasspathResourceLocator(cl, STANDARD_MODULES),
            new ClasspathResourceLocator(cl, "")));
  }

  /**
   * August 2014 - TL
   * added an informative method for returning the actual path used by this resolver
   */
  public String getFullPath() {
    return userFileResourceLocator.describeSearchLocations() + ", " + standardLibraryResourceLocator.describeSearchLocations();
  }

  /**
   * August 2014 - TL
   * added functionality for supplying additional libraries.
   * All usage of this except the one added by TL is supplying libraries  = null
   */
  private static ResourceLocator getLibraryPaths(String[] libraries) {
    List<ResourceLocator> res = new ArrayList<>();

    // First, if userDir is set, search there, otherwise search the current working directory.
    String userDir = ToolIO.getUserDir();
    if (userDir != null) {
      res.add(new FilesystemResourceLocator(Path.of(userDir)));
    } else {
      String cwd = System.getProperty("user.dir");
      if (cwd != null) {
        res.add(new FilesystemResourceLocator(Path.of(cwd)));
      }
    }

    // Next, search the given `libraries` (or the TLA_LIBRARY system property if `libraries` is null).
    String path; // actually a list of paths separated by FileUtil.pathSeparator
    if (libraries == null) path = System.getProperty(TLA_LIBRARY);
    else {
      StringBuffer buf = new StringBuffer();
      for (int i=0; i<libraries.length; i++) {
        buf.append(libraries[i]);
        if (i < libraries.length-1) {
          buf.append(FileUtil.pathSeparator);
        }
      }
      path = buf.toString();
    }
    if (path != null) {
      String[] paths = path.split(FileUtil.pathSeparator);
      for (String s : paths) {
        res.add(new FilesystemResourceLocator(Path.of(s)));
      }
    }

    return new SequentialResourceLocator(res);
  }

  /**
   *  From name, try to find the actual file intended.  If the file is not a normal
   *  file (for instance, if it is an entry in a JAR file), then copy it to the
   *  filesystem and return the copied file.
   *
   *  <p>The name is treated as a filename, not a TLA+ module name; if you are looking
   *  for the Integers module, pass <code>"Integers.tla"</code>.
   *
   *  <p>The first fully-qualified name that refers to a file that actually
   *  exists is the File returned; but if none exists, a non-existent file is returned
   *  anyway.  Hence, the File object returned does not necessarily represent a file
   *  that actually exists in the file system.
   *
   *  @param name the name of the file to look for
   */
  private final TLAFile locate(String name)
  {
    TLAFile userModule = locateAndCopyToFilesystemIfNecessary(userFileResourceLocator, name, false);
    if (userModule != null) {
        return userModule;
    }

    TLAFile libraryModule = locateAndCopyToFilesystemIfNecessary(standardLibraryResourceLocator, name, true);
    if (libraryModule != null) {
        return libraryModule;
    }

    // Small bit of awkwardness here: to preserve the historical FilenameToStream API, this method must return a
    // nonexistent file if the requested one could not be located.  The file we return will be used in error messages
    // about the missing file, so we should return one that looks plausible, but we can't return one that MIGHT exist,
    // because the result will be read if it does!  The approach below correctly synthesizes a non-existent
    // believable-looking path, but relies on the fact that ToolIO.getUserDir() is in the search paths used by
    // userFileResourceLocator---this file does not exist because it has certainly already been searched.
    //
    // In the future, we might improve this pattern by deprecating FilenameToStream and replacing it with a better
    // interface that returns a null/empty result.
    String userDir = ToolIO.getUserDir();
    String parent = userDir == null ? "." : userDir;
    return new TLAFile(parent, name, this);
  } // end locate()

  /**
   * Use the given locator to locate the given file, copying it to the filesystem if necessary.
   *
   * @param locator the locator
   * @param name the file name
   * @param isLibraryModule whether this file should be marked as a standard library module
   * @return the file, or <code>null</code> if it could not be located
   */
  private TLAFile locateAndCopyToFilesystemIfNecessary(ResourceLocator locator, String name, boolean isLibraryModule) {
    try {
      URL location = locator.locate(name);

      if (location == null) {
        return null;
      }

      // Reminder: URL schemes (or "protocols") are supposed to be lower-case, but we are encouraged to be flexible:
      //  > Scheme names consist of a sequence of characters. The lower case
      //  > letters "a"--"z", digits, and the characters plus ("+"), period
      //  > ("."), and hyphen ("-") are allowed. For resiliency, programs
      //  > interpreting URLs should treat upper case letters as equivalent to
      //  > lower case in scheme names (e.g., allow "HTTP" as well as "http").
      // Ref: https://www.ietf.org/rfc/rfc1738.txt
      if ("file".equalsIgnoreCase(location.getProtocol())) {
        Path locationOnFilesystem = Path.of(location.getPath());
        return new TLAFile(locationOnFilesystem, isLibraryModule, this);
      } else {
        try (InputStream in = location.openStream()) {
          return read(name, location, in, isLibraryModule);
        }
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  private TLAFile read(String name, URL location, InputStream is, boolean isLibraryModule) {
	final TLAFile sourceFile = new TLAFile(tmpDir.resolve(name), location, isLibraryModule, this);
	sourceFile.deleteOnExit();
	try {

		final FileOutputStream fos = new FileOutputStream(sourceFile);

		byte buf[] = new byte[1024];
		int len;
		while ((len = is.read(buf)) > 0) {
			fos.write(buf, 0, len);
		}
		fos.close();
		is.close();
	} catch (IOException e) {
		// must not happen
		e.printStackTrace();
	}
	return sourceFile;
  }

  /**
   * Returns a file
   * obtained by some standard method from the string name.  For example,
   * resolve("Foo") might equal the file "/udir/luser/current/path/Foo.tla".
   *
   * Returns null if the file does not exist
   */
  public TLAFile resolve(String name, boolean isModule)
  {
      // Strip off one NEWLINE and anything after it, if it is there
      int n;
      n = name.indexOf( '\n' );
      if ( n >= 0 ) {
          // SZ Feb 20, 2009: the message adjusted to what is actually done
          ToolIO.out.println("*** Warning: module name '" + name + "' contained NEWLINE; "
                  + "Only the part before NEWLINE is considered.");
          name = name.substring( 0, n );     // Strip off the newline
      }
      String sourceFileName = null;
      // SZ Feb 20, 2009:
      // if the name is a name of the module
      if (isModule)
      {
          // SZ Feb 20, 2009:
          // Make sure the file name ends with ".tla".
          if (name.toLowerCase().endsWith(TLAConstants.Files.TLA_EXTENSION))
          {
              name = name.substring(0, (name.length() - TLAConstants.Files.TLA_EXTENSION.length()));
          }
          sourceFileName = name + TLAConstants.Files.TLA_EXTENSION;
      } else
      {
          // SZ Feb 20, 2009: for other files
          // leave the name untouched
          sourceFileName = name;
      }
      // identify the library property
      // extract substrings with getProperty("path.separator");
      // repeat search for each substring until found.
      // locate() the file corresponding to the sourceFileName
      return locate(sourceFileName);
  }

	public File resolve(String name) {
		return resolve(name, false);
	}

	/**
	 * Returns true iff moduleName is the name of a standard module.
	 * This method is used to set the isStandard field of the module's ModuleNode.
	 * I don't know if this is every called with a module that
	 * Added by LL on 24 July 2013.
	 * @see tla2sany.modanalyzer.ParseUnit.isLibraryModule()
	 * @see StandardModules.isDefinedInStandardModule()
	 */
	public boolean isStandardModule(String moduleName) {
		TLAFile file = this.resolve(moduleName, true);
		return file.exists() && file.isLibraryModule();
	}
} // end class
