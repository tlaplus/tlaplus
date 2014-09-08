// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 28 June 2008 at  0:23:49 PST by lamport  

package util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;


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
	
	private static final String TMPDIR = System.getProperty("java.io.tmpdir");
	private static final String STANDARD_MODULES = "tla2sany"
			+ '/' + STANDARD_MODULES_FOLDER + '/';
  
  /**
   * path of directories to be searched in order for the named file.  The setting of 
   * a module's isStandard field depends on the path to the standard modules directory
   * being the last element of this array. 
   */
  private String[] libraryPaths;

  public SimpleFilenameToStream() {
	  libraryPaths = getLibraryPaths(getInstallationBasePath(), null);
  }
  
  public SimpleFilenameToStream(String[] anLibraryPaths) {
	  libraryPaths = getLibraryPaths(getInstallationBasePath(), anLibraryPaths);
  }
  
  // Find the absolute path in the file system to the directory 
  // that is the base of the entire installation of tlaSANY; this path
  // must have separators appropriate to the Unix ('/') or Windows ('\') world.

  private String getInstallationBasePath() {

    // get a "file:" URL for the base directory for package tla2sany
    final URL         url = cl.getResource("tla2sany");

    // jar expanded to the fs (make sure to handle whitespaces correctly
    final String path = url.toString();
	try {
    	// convert to URI which handles paths correctly (even OS dependently)
    	if(!isInJar(path)) {
    	final URI uri = new URI(path);
    		return new File(uri).getAbsolutePath();
    	}
    } catch (URISyntaxException e) {
    	System.err.println(path);
    	// may never happen
    	e.printStackTrace();
    } catch (IllegalArgumentException e) {
    	System.err.println(path);
    	// may never happen
    	e.printStackTrace();
    }
    return path;
   }

  private static boolean isInJar(String aString) {
	return aString.startsWith("jar:");
  }

  public String getFullPath() {
    StringBuffer buf = new StringBuffer();
    String[] ar = libraryPaths;
    for (int i=0; i<ar.length; i++)
    {
      buf.append(ar[i]);
      if (i <ar.length-1) {
        buf.append(", ");
      }
    }
    return buf.toString();
  }

  private String[] getLibraryPaths(final String installationBasePath, String[] libraries) {
    String[] res;
    String path = null;
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
    if (path == null) {
      res = new String[1];
      res[0] = installationBasePath + FileUtil.separator + STANDARD_MODULES_FOLDER + FileUtil.separator;
    }
    else {
      String[] paths = path.split(FileUtil.pathSeparator);
      res = new String[paths.length+1];
      for(int i=0;i<paths.length;i++){
	res[i] = paths[i];
	if (!res[i].endsWith(FileUtil.separator)){
	  res[i] = res[i] + FileUtil.separator;
	}
      }
      res[paths.length] = installationBasePath + FileUtil.separator + STANDARD_MODULES_FOLDER + FileUtil.separator;
    }
    return res;
  }
  
  /**
   *  From name, prepend path elements to try to find the actual
   *  file intended, and use the resulting fully-qualified name to initialize 
   *  the File.  The first fully-qualified name that refers to a file that actually
   *  exists is the File returned; but if none exists, the last one tried is returned 
   *  anyway.  Hence, the File object returned does not necessarily represent a file
   *  that actually exists in the file system.
   *  
   *  @param  module name, used as basis of path name to the file that should contain it
   */
  private final File locate(String name) 
  {

    String prefix      = "";                // directory to be prepended to file name before lookup

    File   sourceFile  = null;              // File object from fully-qualified name of file found by
                                            //   searching "libraryPath" for "name", as is done for PATHs and CLASSPATHs
 
    // The TLA standard modules are presumed to be in a directory tla2sany/StandardModules
    // i.e. a toplevel subdirectory of the main installation directory for SANY
    // We append the StandardModules director to the library path, so the user does
    // not have to do anything special and the standard modules are automatically accessible

    // Debug
    /*
    System.err.println("Installation base path = " + installationBasePath);
    for (int i=0;i<libraryPaths.length;i++)
    {
        System.err.println("libraryPaths = '" + libraryPaths[i] + "'");
    }
    */

    // This code ALWAYS looks in the current directory first for a file (and its capitalization
    // variants), regardless of what the TLA-Library property says the search path should be.
    /***********************************************************************
    * This was modified by LL on 14 May 2008 to change the way sourceFile  *
    * is obtained from sourceFileName.  See the comments for the userDir   *
    * field in util/ToolIO.                                                *
    ***********************************************************************/
    int idx = 0;
    while (true) 
    {
        if ((idx == 0) && (ToolIO.getUserDir() != null)) {
            sourceFile = new File(ToolIO.getUserDir(), name );
        }
        else 
        {
        	// StandardModules contained in jar
        	// need to load files into temp location
        	// from the resource stream
        	//
        	// This would be a lot simpler if TLC would not depend on
        	// File but on InputStream instead
        	if(isInJar(prefix)) {
					InputStream is = cl
							.getResourceAsStream(STANDARD_MODULES
									+ name);
					
				if(is != null) {
					try {
						sourceFile = new File(TMPDIR + File.separator + name);
						sourceFile.deleteOnExit();
						
						FileOutputStream fos = new FileOutputStream(sourceFile);
						
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
				}
        	} else {
        		sourceFile = new File( prefix + name );
        	}
        }
        // Debug
        // System.out.println("Looking for file " + sourceFile);
        if ( sourceFile.exists() )  break;
        if (idx >= libraryPaths.length) break;
        prefix = libraryPaths[idx++];
    } // end while

    return sourceFile;

  } // end locate()

  /**
   * Returns a file
   * obtained by some standard method from the string name.  For example,
   * resolve("Foo") might equal the file "/udir/luser/current/path/Foo.tla".
   * 
   * Returns null if the file does not exist
   */ 
  public File resolve(String name, boolean isModule)
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
          if (name.toLowerCase().endsWith(".tla")) 
          {
              name = name.substring(0, name.length() - 4);
          }
          sourceFileName = name + ".tla";
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
	 * Returns true iff moduleName is the name of a standard module.  It
	 * assumes the empirically determined fact that libraryPaths is set to
	 * have the path of the standard modules as the last element of the array.
	 * This method is used to set the isStandard field of the module's ModuleNode.
	 * I don't know if this is every called with a module that 
	 * Added by LL on 24 July 2013.
	 */
	public boolean isStandardModule(String moduleName) {
		 File file = this.resolve(moduleName, true) ;
		 if (file == null) {
			 return false ; 
			 }
		 String path = file.getAbsolutePath() ;
		 if (path == null) {
			 return false ;
		 }
	     return path.startsWith(this.libraryPaths[this.libraryPaths.length - 1] ) ;
	}
} // end class
