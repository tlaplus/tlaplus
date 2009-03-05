package de.techjava.tla.ui.extensions;

/**
 * Simple IProblemHolder implementation
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: SimpleProblemHolder.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class SimpleProblemHolder 
	implements IProblemHolder 
{
    private ILocation location;
    private int type;
    private String message;
    
    public SimpleProblemHolder(ILocation location, String message, int type)
    {
        this.location = location;
        this.message = message;
        this.type = type;
    }
    
    
    public ILocation getLocation() {
        return location;
    }
    public void setLocation(ILocation location) {
        this.location = location;
    }
    public String getMessage() {
        return message;
    }
    public void setMessage(String message) {
        this.message = message;
    }
    public int getType() {
        return type;
    }
    public void setType(int type) {
        this.type = type;
    }
}

/*
 * $Log: SimpleProblemHolder.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */