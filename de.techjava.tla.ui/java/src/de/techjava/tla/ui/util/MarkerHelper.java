package de.techjava.tla.ui.util;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.editors.TLAEditor;
import de.techjava.tla.ui.extensions.IProblemHolder;

/**
 * A toolkit with usefull marker functions
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: MarkerHelper.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class MarkerHelper 
{
    /**
     * TODO better support for UI Thread
     * TODO check why the fileview is not containing the markers
     * Creates an attribute map for a marker on a given file
     * This method is private because it has to be started from a UI-Thread
     * use MarkerHelper#createMarker()
     * 
     * @param file file to mark
     * @param holder a problem holder containing location and error message
     * @param severity severity of the problem IMarker.ERROR, IMarker.WARNING
     * @param priority priority of the problem IMarker.HIGH, IMarker.NORMAL, IMarker.LOW
     * @return an attribute map for the marker
     */
    public static Map getMarkerAttributes(
            	IFile file, 
            	IProblemHolder holder, 
            	int severity, 
            	int priority
            )
    {
        Map attributes 	= new HashMap(11);
        int line 		= holder.getLocation().beginLine() - 1;
        int startChar	= -1;
        int endChar 	= -1;
        int offset 		= 0;
        try 
        {
	        
	        IWorkbenchWindow[] workbenchWindows = UIPlugin.getDefault().getWorkbench().getWorkbenchWindows();
	        IWorkbenchPage activePage = null;
	        if (workbenchWindows.length == 1) 
	        {
	            activePage  = workbenchWindows[0].getActivePage();
	        } else {
	            
	            return attributes;
	        }
	        FileEditorInput fileEditorInput = new FileEditorInput(file);
	        IEditorPart editorPart = activePage.findEditor(fileEditorInput);
	        if (editorPart != null && editorPart instanceof TLAEditor)
	        {
	            ITextEditor editor 		= (ITextEditor)editorPart;
	            
	            IDocument	document 	= editor.getDocumentProvider().getDocument(fileEditorInput);
	            
	            
	            
	            try 
	            {
	                IRegion lineRegion 	= document.getLineInformation(line);
	                
	                String 		textLine 	= document.get(lineRegion.getOffset(), lineRegion.getLength());
	                
	                offset 				= lineRegion.getOffset();
	                startChar			= offset + getRealOffset(textLine, holder.getLocation().beginColumn() - 1);
	                endChar				= offset + getRealOffset(textLine, holder.getLocation().endColumn());
	                
	                
	            } catch (BadLocationException e) 
	            {
	                // ignore
	            }
	            
	            attributes.put(IMarker.LINE_NUMBER, new Integer(line));
	            attributes.put(IMarker.CHAR_START, new Integer(startChar));
	            attributes.put(IMarker.CHAR_END, new Integer(endChar));
	            attributes.put(IMarker.MESSAGE, holder.getMessage());
	            attributes.put(IMarker.SEVERITY, new Integer(severity));
	            attributes.put(IMarker.PRIORITY, new Integer(priority));
	        }
        } catch (Exception e) 
        {
            e.printStackTrace();
        }

	    return attributes;
    }
    /**
     * Creates a marker on a resource
     * @param markerID
     * @param resource
     * @param holder
     * @param severity
     * @param priority
     * @throws CoreException
     */
    public static void createMarker(
            final String markerID,
            final IResource resource, 
            final IProblemHolder holder,
            final int severity,
            final int priority)
    	throws CoreException
    {
        IWorkspaceRunnable workspaceRunnable = new IWorkspaceRunnable()
        {
            /**
             * @see org.eclipse.core.resources.IWorkspaceRunnable#run(org.eclipse.core.runtime.IProgressMonitor)
             */
            public void run(IProgressMonitor monitor) 
            	throws CoreException 
            {
                IMarker marker = resource.createMarker(markerID);
                marker.setAttributes(getMarkerAttributes((IFile)resource, holder, severity, priority));
            }
        };
        
        resource.getWorkspace().run(workspaceRunnable, null, IWorkspace.AVOID_UPDATE, null);
    }
    /**
     * Gives the offset inside the line taking aware of tabs
     * @param offset the offset in that a tab length is 1
     * @param line the line
     * @return offset in the line, in which the tab width us 4.
     */
    public static int getRealOffset(String line, int offset)
    {
        int TAB_WIDTH = 8;
        if (line.indexOf("\t") == -1) 
        {
            
            return Math.min(offset, line.length());
        } else 
        {
            int realOffset = offset;
            int modificator = 0;
            // tab is inside the line
            for (int i = 0; i != -1; i = line.indexOf("\t", i+1))
            {
                if (i < offset) 
                {
                    
                    int tabLength = ( (i + modificator) / TAB_WIDTH + 1 ) * TAB_WIDTH - (i + modificator) ;
                    // realOffset -= 7;
                    
                    // System.out.println("i :" + (i + modificator) + " tabLength " + tabLength);
                    modificator += (tabLength - 1);
                    realOffset = realOffset - (tabLength - 1) ;
                }
            }
            // System.out.println("Line : \"" + line + "\"" + " offset " + offset + " real ofsset " + realOffset);
            return realOffset;
        }
    }
}

/*
 * $Log: MarkerHelper.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/11/03 14:51:14  sza
 * marker position computation awaring tabs
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 *
 */