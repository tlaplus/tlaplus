// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Wed Jul 11 00:00:55 PDT 2001 by yuanyu
package util;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.Serializable;

import tlc2.output.EC;
import tlc2.tool.distributed.InternRMI;

/**
 * Storage for the UniqueStrings.  It stores them in a hash table using
 * simple linear hashing.
 * @see {@link UniqueString} for more information 
 * @author Yuan Yu, Simon Zambrovski
 */
public final class InternTable implements Serializable
{

    private int count;  // The number of entries in the table.
    private int length; // The length of the table.
    private int thresh; // The maximum number of entries before the table
                        // needs to be grown.
    private UniqueString[] table;  // The array that holds the entries.

    // SZ 10.04.2009: removed unused variable
    // made token counter to instance variable, since there is only one instance of the InternTable
    private int tokenCnt = 0; // the token counter

     private InternRMI internSource = null;

    public InternTable(int size)
    {
        this.table = new UniqueString[size];
        this.count = 0;
        this.length = size;
        this.thresh = this.length / 2;
    }
    
    private void grow()
    {
        UniqueString[] old = this.table;
        this.count = 0;
        this.length = 2 * this.length + 1;
        this.thresh = this.length / 2;
        this.table = new UniqueString[this.length];
        for (int i = 0; i < old.length; i++)
        {
            UniqueString var = old[i];
            if (var != null)
                this.put(var);
        }
    }

    private void put(UniqueString var)
    {
        // The following statement was added on 14 Feb 2012 by M.K.  
        // It calls the grow() method to enlarge the hash table storing
        // UniqueStrings.  This put() method is called both by the 
        // grow() method, and by the recover() method,
        // which is used to recreate the hash table when restarting from
        // a checkpoint.  The second use was apparently forgotten by Yuan Yu 
        // in the original code, which never called the grow() method,
        // causing TLC to hang when restarting from a checkpoint
        // for a spec in which the table had grown.  Amazingly, this was
        // never discovered in approximately 10 years of use.
        if (this.count >= this.thresh)
            this.grow();
        
        int loc = (var.hashCode() & 0x7FFFFFFF) % length;
        while (true)
        {
            UniqueString ent = this.table[loc];
            if (ent == null)
            {
                this.table[loc] = var;
                this.count++;
                return;
            }
            loc = (loc + 1) % length;
        }
    }

    /**
     * If there exists a UniqueString object obj such that obj.getTok()
     * equals id, then get(id) returns obj; otherwise, it returns null.
     */
    public UniqueString get(int id)
    {
        for (int i = 0; i < this.table.length; i++)
        {
            UniqueString var = this.table[i];
            if (var != null && var.getTok() == id)
            {
                return var;
            }
        }
        return null;
    }

    /**
     * Create the unique string based on the token
     */
//    private UniqueString create(String str)
//    {
//        return new UniqueString(str, ++tokenCnt);
//    }

	private UniqueString create(String str) {
		if (this.internSource == null) {
			return new UniqueString(str, ++tokenCnt);
		}
		try {
			return this.internSource.intern(str);
		} catch (Exception e) {
			Assert.fail("Failed to intern " + str + ".");
		}
		return null; // make compiler happy
	}

    public UniqueString put(String str)
    {
        synchronized (InternTable.class)
        {
            if (this.count >= this.thresh)
                this.grow();
            int loc = (str.hashCode() & 0x7FFFFFFF) % length;
            while (true)
            {
                UniqueString ent = this.table[loc];
                if (ent == null)
                {
                    UniqueString var = this.create(str);
                    this.table[loc] = var;
                    this.count++;
                    return var;
                }
                if (ent.toString().equals(str))
                {
                    return ent;
                }
                loc = (loc + 1) % length;
            }
        }
    }

    public void beginChkpt(String filename) throws IOException
    {
        BufferedDataOutputStream dos = new BufferedDataOutputStream(this.chkptName(filename, "tmp"));
        dos.writeInt(tokenCnt);
        for (int i = 0; i < this.table.length; i++)
        {
            UniqueString var = this.table[i];
            if (var != null)
                var.write(dos);
        }
        dos.close();
    }

    public void commitChkpt(String filename) throws IOException
    {
        File oldChkpt = new File(this.chkptName(filename, "chkpt"));
        File newChkpt = new File(this.chkptName(filename, "tmp"));
        if ((oldChkpt.exists() && !oldChkpt.delete()) || !newChkpt.renameTo(oldChkpt))
        {
            throw new IOException("InternTable.commitChkpt: cannot delete " + oldChkpt);
        }
    }

    public synchronized void recover(String filename) throws IOException
    {
        BufferedDataInputStream dis = new BufferedDataInputStream(this.chkptName(filename, "chkpt"));
        tokenCnt = dis.readInt();
        try
        {
            while (!dis.atEOF())
            {
                UniqueString var = UniqueString.read(dis);
                this.put(var);
            }
        } catch (EOFException e)
        {
            Assert.fail(EC.SYSTEM_CHECKPOINT_RECOVERY_CORRUPT, e.getMessage());
        }
        dis.close();
    }

    private String chkptName(String filename, String ext)
    {
        return filename + FileUtil.separator + "vars." + ext;
    }

	public void setSource(InternRMI source) {
		this.internSource = source;
	}

}
